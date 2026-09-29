const std = @import("std");
pub fn main() !void {
    var buf: [64]u8 = undefined;
    var w = std.fs.File.stdout().writer(&buf);
    try w.interface.print("hello {s}\n", .{"world"});
    try w.interface.flush();
}
