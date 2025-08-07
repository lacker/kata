const std = @import("std");

fn greet(comptime name: []const u8) []const u8 {
    return "Hello, " ++ name ++ "!";
}

fn printLine(msg: []const u8) !void {
    try std.io.getStdOut().writer().print("{s}\n", .{msg});
}

pub fn main() !void {
    const msg = greet("world"); // evaluated entirely at compile time
    printLine(msg);
}
