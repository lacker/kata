const std = @import("std");

fn greet(comptime name: []const u8) []const u8 {
    return "Hello, " ++ name ++ "!";
}

pub fn main() !void {
    const msg = greet("world"); // evaluated entirely at compile time
    try std.io.getStdOut().writer().print("{s}\n", .{msg});
}
