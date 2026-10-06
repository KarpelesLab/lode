//! Debug information for `lode build -g`: DWARF line tables and functions.
//!
//! LatticeFoundry emits DWARF for one source file: each IR instruction has a
//! line number, and its line table maps machine code to those numbers. A
//! Lode program comes from several files (the root file and every package
//! it imports, the standard library's too), so lowering numbers the source
//! lines it uses instead ([`Lowered::lines`](crate::lower::Lowered::lines)):
//! IR line `n` stands for a file and a line. This module reads LF's line
//! table back (which code is at which IR line, function by function), and
//! replaces LF's debug sections with its own, in terms of the real files
//! and lines:
//!
//! - `.debug_info`: one compile unit, named after the root file, with one
//!   `DW_TAG_subprogram` per function (its symbol as the name, its address
//!   range, the file and line it's declared at);
//! - `.debug_line`: a line-number program over every source file, one
//!   sequence per function;
//! - `.debug_abbrev`: the shapes of those entries.
//!
//! Strings are inline (`DW_FORM_string`), so there's no `.debug_str`.
//! Addresses are `Abs64` relocations against the function symbols, which
//! the linker fills. Local variables and types aren't described yet.

use std::collections::HashMap;

use latticefoundry::mc::emit::{Emitted, Emitter, Ref};
use latticefoundry::mc::object::{
    ObjectModule, RelocKind, Relocation, SectionId, SymbolType, SymbolValue,
};

use crate::source::{FileId, SourceMap};

const DW_TAG_COMPILE_UNIT: u64 = 0x11;
const DW_TAG_SUBPROGRAM: u64 = 0x2e;

const DW_AT_NAME: u64 = 0x03;
const DW_AT_STMT_LIST: u64 = 0x10;
const DW_AT_LOW_PC: u64 = 0x11;
const DW_AT_HIGH_PC: u64 = 0x12;
const DW_AT_COMP_DIR: u64 = 0x1b;
const DW_AT_PRODUCER: u64 = 0x25;
const DW_AT_DECL_FILE: u64 = 0x3a;
const DW_AT_DECL_LINE: u64 = 0x3b;
const DW_AT_EXTERNAL: u64 = 0x3f;

const DW_FORM_ADDR: u64 = 0x01;
const DW_FORM_DATA8: u64 = 0x07;
const DW_FORM_STRING: u64 = 0x08;
const DW_FORM_FLAG: u64 = 0x0c;
const DW_FORM_UDATA: u64 = 0x0f;
const DW_FORM_SEC_OFFSET: u64 = 0x17;

const DW_LNS_COPY: u8 = 1;
const DW_LNS_ADVANCE_PC: u8 = 2;
const DW_LNS_ADVANCE_LINE: u8 = 3;
const DW_LNS_SET_FILE: u8 = 4;
const DW_LNS_CONST_ADD_PC: u8 = 8;
const DW_LNS_FIXED_ADVANCE_PC: u8 = 9;
const DW_LNE_END_SEQUENCE: u8 = 1;
const DW_LNE_SET_ADDRESS: u8 = 2;

/// The line program's header parameters (LF's, the usual ones).
const LINE_BASE: i8 = -5;
const LINE_RANGE: u8 = 14;
const OPCODE_BASE: u8 = 13;

/// One function's rows, as LF's line table gives them: its symbol, and
/// `(offset in the function, IR line number)` in address order. The first
/// row is LF's entry row, at the function's declaration.
#[derive(Debug)]
struct FuncRows {
    symbol: String,
    rows: Vec<(u64, u32)>,
}

/// Replace the DWARF sections LatticeFoundry put in `object` (whose line
/// numbers are IR line numbers, `lines` giving the source line of each)
/// by Lode's, over the source files of `files`. `root` names the compile
/// unit, and `comp_dir` is the directory relative file names are in.
pub fn rewrite(
    object: &ObjectModule,
    lines: &[(FileId, u32)],
    files: &SourceMap,
    root: FileId,
    comp_dir: &str,
) -> Result<ObjectModule, String> {
    let funcs = read_lines(object)?;
    let mut out = without_debug(object);

    // Where each function is, and its size.
    let mut place: HashMap<&str, (u64, u64)> = HashMap::new();
    for sym in object.symbols() {
        if sym.kind == SymbolType::Func
            && let SymbolValue::Defined { offset, .. } = sym.value
        {
            place.insert(&sym.name, (offset, sym.size));
        }
    }
    let source = |id: u32| -> Result<(FileId, u32), String> {
        id.checked_sub(1)
            .and_then(|i| lines.get(i as usize))
            .copied()
            .ok_or_else(|| format!("no source line for IR line {id}"))
    };

    // The files, in the order the functions use them (the root's first),
    // numbered from 1.
    let mut file_ids: Vec<FileId> = vec![root];
    let mut file_index = |file: FileId| -> u64 {
        match file_ids.iter().position(|&f| f == file) {
            Some(i) => i as u64 + 1,
            None => {
                file_ids.push(file);
                file_ids.len() as u64
            }
        }
    };

    let mut units = Vec::new();
    for f in &funcs {
        let &(start, size) = place
            .get(f.symbol.as_str())
            .ok_or_else(|| format!("no function symbol `{}`", f.symbol))?;
        let decl = f
            .rows
            .first()
            .map_or(Ok((root, 1)), |&(_, id)| source(id))?;
        let mut rows: Vec<(u64, u64, u32)> = Vec::new();
        for &(off, id) in &f.rows {
            let (file, line) = source(id)?;
            let row = (off, file_index(file), line);
            match rows.last_mut() {
                // A later row at the same address replaces the earlier one.
                Some(last) if last.0 == off => *last = row,
                Some(last) if (last.1, last.2) == (row.1, row.2) => {}
                _ => rows.push(row),
            }
        }
        units.push(Unit {
            symbol: f.symbol.clone(),
            start,
            size,
            decl_file: file_index(decl.0),
            decl_line: decl.1,
            rows,
        });
    }

    let names: Vec<&str> = file_ids
        .iter()
        .map(|&f| files.get(f).name.as_str())
        .collect();
    out.add_section(debug_section(".debug_abbrev", abbrev()));
    out.add_emitted_section(
        ".debug_info",
        latticefoundry::mc::object::SectionKind::Debug,
        1,
        info(&units, names[0], comp_dir),
    );
    out.add_emitted_section(
        ".debug_line",
        latticefoundry::mc::object::SectionKind::Debug,
        1,
        line_program(&units, &names),
    );
    Ok(out)
}

/// A function, for Lode's DWARF: its symbol, where it is in `.text` and
/// its size, the file (an index in the line table's files) and line it's
/// declared at, and its rows: `(offset, file, line)`.
struct Unit {
    symbol: String,
    start: u64,
    size: u64,
    decl_file: u64,
    decl_line: u32,
    rows: Vec<(u64, u64, u32)>,
}

/// A copy of `object` without its `.debug_*` sections (and their
/// relocations).
fn without_debug(object: &ObjectModule) -> ObjectModule {
    let mut out = ObjectModule::new(object.name.clone());
    let mut ids: Vec<Option<SectionId>> = Vec::new();
    for s in object.sections() {
        ids.push((!s.name.starts_with(".debug_")).then(|| out.add_section(s.clone())));
    }
    for sym in object.symbols() {
        let mut sym = sym.clone();
        if let SymbolValue::Defined { section, offset } = sym.value {
            let section = ids[section.index()].expect("no symbol is in a debug section");
            sym.value = SymbolValue::Defined { section, offset };
        }
        out.add_symbol(sym);
    }
    for r in object.relocations() {
        if let Some(section) = ids[r.section.index()] {
            out.add_relocation(Relocation { section, ..*r });
        }
    }
    out
}

/// Read the functions' rows from the `.debug_line` section LF emitted: a
/// DWARF line-number program with one sequence per function, each starting
/// with `DW_LNE_set_address` relocated against the function's symbol.
fn read_lines(object: &ObjectModule) -> Result<Vec<FuncRows>, String> {
    let Some(index) = object
        .sections()
        .iter()
        .position(|s| s.name == ".debug_line")
    else {
        return Ok(Vec::new());
    };
    let section = SectionId::from_index(index);
    let symbol_at: HashMap<u64, &str> = object
        .relocations()
        .iter()
        .filter(|r| r.section == section)
        .map(|r| (r.offset, object.symbol(r.symbol).name.as_str()))
        .collect();
    let bytes = &object.section(section).bytes;
    let bad = || "LatticeFoundry's .debug_line can't be read".to_owned();
    let mut r = Reader { bytes, at: 0 };

    // The header (DWARF 4, 32-bit).
    let unit_length = r.u32().ok_or_else(bad)? as usize;
    let end = (4 + unit_length).min(bytes.len());
    let _version = r.u16().ok_or_else(bad)?;
    let header_length = r.u32().ok_or_else(bad)? as usize;
    let program = r.at + header_length;
    let min_inst = u64::from(r.u8().ok_or_else(bad)?);
    let _max_ops = r.u8().ok_or_else(bad)?;
    let _default_is_stmt = r.u8().ok_or_else(bad)?;
    let line_base = i64::from(r.u8().ok_or_else(bad)? as i8);
    let line_range = r.u8().ok_or_else(bad)?;
    let opcode_base = r.u8().ok_or_else(bad)?;
    let lengths: Vec<u8> = (1..opcode_base)
        .map(|_| r.u8())
        .collect::<Option<_>>()
        .ok_or_else(bad)?;
    r.at = program;

    let mut funcs: Vec<FuncRows> = Vec::new();
    let mut addr: u64 = 0;
    let mut line: i64 = 1;
    let mut current: Option<FuncRows> = None;
    while r.at < end {
        let op = r.u8().ok_or_else(bad)?;
        match op {
            0 => {
                let len = r.uleb().ok_or_else(bad)? as usize;
                let next = r.at + len;
                let sub = r.u8().ok_or_else(bad)?;
                match sub {
                    DW_LNE_SET_ADDRESS => {
                        let symbol = symbol_at.get(&(r.at as u64)).ok_or_else(bad)?;
                        current = Some(FuncRows {
                            symbol: (*symbol).to_owned(),
                            rows: Vec::new(),
                        });
                        addr = 0;
                    }
                    DW_LNE_END_SEQUENCE => {
                        funcs.extend(current.take());
                        addr = 0;
                        line = 1;
                    }
                    _ => {}
                }
                r.at = next;
            }
            DW_LNS_COPY => {
                let f = current.as_mut().ok_or_else(bad)?;
                f.rows.push((addr, u32::try_from(line).map_err(|_| bad())?));
            }
            DW_LNS_ADVANCE_PC => addr += r.uleb().ok_or_else(bad)? * min_inst,
            DW_LNS_ADVANCE_LINE => line += r.sleb().ok_or_else(bad)?,
            DW_LNS_CONST_ADD_PC => {
                addr += u64::from((255 - opcode_base) / line_range) * min_inst;
            }
            DW_LNS_FIXED_ADVANCE_PC => addr += u64::from(r.u16().ok_or_else(bad)?),
            op if op >= opcode_base => {
                let adjusted = op - opcode_base;
                addr += u64::from(adjusted / line_range) * min_inst;
                line += line_base + i64::from(adjusted % line_range);
                let f = current.as_mut().ok_or_else(bad)?;
                f.rows.push((addr, u32::try_from(line).map_err(|_| bad())?));
            }
            // Other standard opcodes: skip their operands.
            op => {
                for _ in 0..lengths[op as usize - 1] {
                    r.uleb().ok_or_else(bad)?;
                }
            }
        }
    }
    Ok(funcs)
}

/// A cursor over little-endian DWARF data.
struct Reader<'a> {
    bytes: &'a [u8],
    at: usize,
}

impl Reader<'_> {
    fn take<const N: usize>(&mut self) -> Option<[u8; N]> {
        let b = self.bytes.get(self.at..self.at + N)?.try_into().ok()?;
        self.at += N;
        Some(b)
    }

    fn u8(&mut self) -> Option<u8> {
        self.take::<1>().map(|b| b[0])
    }

    fn u16(&mut self) -> Option<u16> {
        self.take().map(u16::from_le_bytes)
    }

    fn u32(&mut self) -> Option<u32> {
        self.take().map(u32::from_le_bytes)
    }

    fn uleb(&mut self) -> Option<u64> {
        let mut v = 0u64;
        let mut shift = 0;
        loop {
            let b = self.u8()?;
            if shift < 64 {
                v |= u64::from(b & 0x7f) << shift;
            }
            shift += 7;
            if b & 0x80 == 0 {
                return Some(v);
            }
        }
    }

    fn sleb(&mut self) -> Option<i64> {
        let mut v = 0i64;
        let mut shift = 0;
        loop {
            let b = self.u8()?;
            if shift < 64 {
                v |= i64::from(b & 0x7f) << shift;
            }
            shift += 7;
            if b & 0x80 == 0 {
                if shift < 64 && b & 0x40 != 0 {
                    v |= -1 << shift;
                }
                return Some(v);
            }
        }
    }
}

fn uleb(buf: &mut Vec<u8>, mut v: u64) {
    loop {
        let byte = (v & 0x7f) as u8;
        v >>= 7;
        if v == 0 {
            buf.push(byte);
            return;
        }
        buf.push(byte | 0x80);
    }
}

fn sleb(buf: &mut Vec<u8>, mut v: i64) {
    loop {
        let byte = (v & 0x7f) as u8;
        v >>= 7;
        if (v == 0 && byte & 0x40 == 0) || (v == -1 && byte & 0x40 != 0) {
            buf.push(byte);
            return;
        }
        buf.push(byte | 0x80);
    }
}

fn uleb_e(e: &mut Emitter, v: u64) {
    let mut b = Vec::new();
    uleb(&mut b, v);
    e.bytes(&b);
}

fn sleb_e(e: &mut Emitter, v: i64) {
    let mut b = Vec::new();
    sleb(&mut b, v);
    e.bytes(&b);
}

fn string_e(e: &mut Emitter, s: &str) {
    e.bytes(s.as_bytes());
    e.u8(0);
}

fn debug_section(name: &str, bytes: Vec<u8>) -> latticefoundry::mc::object::Section {
    let mut s = latticefoundry::mc::object::Section::new(
        name,
        latticefoundry::mc::object::SectionKind::Debug,
        1,
    );
    s.bytes = bytes;
    s
}

/// An abbreviation: its code, its tag, whether entries of it have
/// children, and its attributes with their forms.
type Abbrev = (u64, u64, bool, &'static [(u64, u64)]);

/// The abbreviations: 1, the compile unit; 2, a function.
fn abbrev() -> Vec<u8> {
    let mut b = Vec::new();
    let entries: [Abbrev; 2] = [
        (
            1,
            DW_TAG_COMPILE_UNIT,
            true,
            &[
                (DW_AT_PRODUCER, DW_FORM_STRING),
                (DW_AT_NAME, DW_FORM_STRING),
                (DW_AT_COMP_DIR, DW_FORM_STRING),
                (DW_AT_STMT_LIST, DW_FORM_SEC_OFFSET),
                (DW_AT_LOW_PC, DW_FORM_ADDR),
                (DW_AT_HIGH_PC, DW_FORM_DATA8),
            ],
        ),
        (
            2,
            DW_TAG_SUBPROGRAM,
            false,
            &[
                (DW_AT_EXTERNAL, DW_FORM_FLAG),
                (DW_AT_NAME, DW_FORM_STRING),
                (DW_AT_DECL_FILE, DW_FORM_UDATA),
                (DW_AT_DECL_LINE, DW_FORM_UDATA),
                (DW_AT_LOW_PC, DW_FORM_ADDR),
                (DW_AT_HIGH_PC, DW_FORM_DATA8),
            ],
        ),
    ];
    for (code, tag, children, attrs) in entries {
        uleb(&mut b, code);
        uleb(&mut b, tag);
        b.push(u8::from(children));
        for &(at, form) in attrs {
            uleb(&mut b, at);
            uleb(&mut b, form);
        }
        b.extend([0, 0]);
    }
    b.push(0);
    b
}

/// `.debug_info`: the compile unit, and a subprogram for each function.
fn info(units: &[Unit], name: &str, comp_dir: &str) -> Emitted {
    let mut e = Emitter::new();
    e.u32(0); // unit_length, patched below
    e.u16(4); // version
    e.u32(0); // debug_abbrev_offset
    e.u8(8); // address_size

    uleb_e(&mut e, 1);
    string_e(&mut e, &format!("lode {}", crate::VERSION));
    string_e(&mut e, name);
    string_e(&mut e, comp_dir);
    e.u32(0); // stmt_list
    // The functions are in address order: the unit spans from the first
    // one's start to the last one's end.
    match (units.first(), units.last()) {
        (Some(first), Some(last)) => {
            e.reference(RelocKind::Abs64, Ref::Symbol(first.symbol.clone()), 0);
            e.u64(last.start + last.size - first.start);
        }
        _ => {
            e.u64(0);
            e.u64(0);
        }
    }

    for u in units {
        uleb_e(&mut e, 2);
        e.u8(1); // external
        string_e(&mut e, &u.symbol);
        uleb_e(&mut e, u.decl_file);
        uleb_e(&mut e, u64::from(u.decl_line));
        e.reference(RelocKind::Abs64, Ref::Symbol(u.symbol.clone()), 0);
        e.u64(u.size);
    }
    e.u8(0); // end of the unit's children

    let mut out = e.finish().expect("no labels");
    let len = out.bytes.len() as u32 - 4;
    out.bytes[..4].copy_from_slice(&len.to_le_bytes());
    out
}

/// `.debug_line`: the files, then one sequence per function.
fn line_program(units: &[Unit], files: &[&str]) -> Emitted {
    let mut e = Emitter::new();
    e.u32(0); // unit_length, patched below
    e.u16(4); // version
    e.u32(0); // header_length, patched below
    let header_start = e.offset();
    e.u8(1); // minimum_instruction_length
    e.u8(1); // maximum_operations_per_instruction
    e.u8(1); // default_is_stmt
    e.u8(LINE_BASE as u8);
    e.u8(LINE_RANGE);
    e.u8(OPCODE_BASE);
    e.bytes(&[0, 1, 1, 1, 1, 0, 0, 0, 1, 0, 0, 1]); // standard_opcode_lengths
    e.u8(0); // no include_directories: names are relative to comp_dir
    for name in files {
        string_e(&mut e, name);
        e.bytes(&[0, 0, 0]); // directory, mtime, length
    }
    e.u8(0);
    let header_length = (e.offset() - header_start) as u32;

    for u in units {
        e.u8(0);
        uleb_e(&mut e, 9);
        e.u8(DW_LNE_SET_ADDRESS);
        e.reference(RelocKind::Abs64, Ref::Symbol(u.symbol.clone()), 0);
        let (mut addr, mut file, mut line) = (0u64, 1u64, 1i64);
        for &(off, f, l) in &u.rows {
            if f != file {
                e.u8(DW_LNS_SET_FILE);
                uleb_e(&mut e, f);
                file = f;
            }
            if off > addr {
                e.u8(DW_LNS_ADVANCE_PC);
                uleb_e(&mut e, off - addr);
                addr = off;
            }
            if i64::from(l) != line {
                e.u8(DW_LNS_ADVANCE_LINE);
                sleb_e(&mut e, i64::from(l) - line);
                line = i64::from(l);
            }
            e.u8(DW_LNS_COPY);
        }
        if u.size > addr {
            e.u8(DW_LNS_ADVANCE_PC);
            uleb_e(&mut e, u.size - addr);
        }
        e.bytes(&[0, 1, DW_LNE_END_SEQUENCE]);
    }

    let mut out = e.finish().expect("no labels");
    out.bytes[6..10].copy_from_slice(&header_length.to_le_bytes());
    let len = out.bytes.len() as u32 - 4;
    out.bytes[..4].copy_from_slice(&len.to_le_bytes());
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn leb128_round_trips() {
        for v in [
            0i64,
            1,
            -1,
            63,
            64,
            -64,
            -65,
            127,
            128,
            -12345,
            i64::MAX,
            i64::MIN,
        ] {
            let mut b = Vec::new();
            sleb(&mut b, v);
            assert_eq!(Reader { bytes: &b, at: 0 }.sleb(), Some(v), "{v}");
        }
        for v in [0u64, 1, 127, 128, 300, u64::MAX] {
            let mut b = Vec::new();
            uleb(&mut b, v);
            assert_eq!(Reader { bytes: &b, at: 0 }.uleb(), Some(v), "{v}");
        }
    }
}
