const std = @import("std");
const Formula = @import("model.zig").Formula;
const Clause = @import("model.zig").Clause;

/// assumes that the given path is relative to the current working directory
/// dimacs sample file for (a | b) & (!a | !b), comments not part of the file:
/// p cnf 3 2
/// 1 2 0       % clause 1: a | b
/// -1 -2 0     % clause 2: !a | !b
pub fn parseDimacs(allocator: std.mem.Allocator, dimacs_file_path: []const u8) !Formula {
    var formula = Formula.init(allocator);
    errdefer formula.deinit();

    const file = try std.fs.cwd().openFile(dimacs_file_path, .{});
    defer file.close();

    const reader = file.reader();

    while (try reader.readUntilDelimiterOrEofAlloc(allocator, '\n', 1024)) |line| {
        if (line.len == 0 or line[0] == 'c' or line[0] == 'p') {
            continue;
        }

        const clause = try parseDimacsClauseLine(allocator, line);
        formula.append(clause) catch unreachable;
    }

    return formula;
}

fn parseDimacsClauseLine(allocator: std.mem.Allocator, line: []const u8) !Clause(Formula.LiteralType) {
    var clause = Clause(Formula.LiteralType).init(allocator);
    errdefer clause.deinit();

    var tokens = std.mem.tokenizeScalar(u8, line, ' ');
    while (tokens.next()) |token| {
        const lit = try std.fmt.parseInt(Formula.LiteralType, token, 10);
        if (lit == 0) {
            break;
        }

        clause.add(lit);
    }

    return clause;
}

test parseDimacsClauseLine {
    {
        var clause = try parseDimacsClauseLine(std.testing.allocator, "1 2 3 20 -1337 0");
        defer clause.deinit();

        try std.testing.expect(clause.eqToSlice(&[_]Formula.LiteralType{ 1, 2, 3, 20, -1337 }));
    }

    {
        var clause = try parseDimacsClauseLine(std.testing.allocator, "1337 -90 1 1 1 1 -1 0 0");
        defer clause.deinit();

        try std.testing.expect(clause.eqToSlice(&[_]Formula.LiteralType{ 1337, -90, 1, -1 }));
    }

    {
        var clause = try parseDimacsClauseLine(std.testing.allocator, "0 0 0");
        defer clause.deinit();

        try std.testing.expect(clause.isEmpty());
    }
}
