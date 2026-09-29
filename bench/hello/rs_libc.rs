unsafe extern "C" { fn write(fd: i32, buf: *const u8, n: usize) -> isize; }
fn main() { unsafe { write(1, b"hello world\n".as_ptr(), 12); } }
