const std = @import("std");
pub fn main() void {
    _ = std.posix.system.write(1, "hello world\n", 12);
}
