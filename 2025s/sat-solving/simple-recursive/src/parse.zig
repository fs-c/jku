const std = @import("std");

/// assumes that the given path is relative to the current working directory
/// dimacs sample file for (a | b) & (!a | !b), comments not part of the file:
/// p cnf 3 2
/// 1 2 0       % clause 1: a | b
/// -1 -2 0     % clause 2: !a | !b
///
/// returns an array of arrays of integers, where integers are the literals (negative = negated),
/// inner arrays are the clauses, outer array is the conjunction
///
/// caller must free the returned data (both the clauses and the array of clauses!)
pub fn parseDimacs(allocator: std.mem.Allocator, dimacs_file_path: []const u8) !std.ArrayList(std.ArrayList(i32)) {
    var clauses = std.ArrayList(std.ArrayList(i32)).init(allocator);
    errdefer clauses.deinit();

    const file = try std.fs.cwd().openFile(dimacs_file_path, .{});
    defer file.close();

    const reader = file.reader();

    // var num_vars: usize = 0;
    // var num_clauses: usize = 0;

    // if (try reader.readUntilDelimiterOrEofAlloc(allocator, '\n', 128)) |first_line| {
    //     // skip the `p cnf ` prefix
    //     const tokens = std.mem.tokenizeScalar(u8, first_line[6..], ' ');
    //     num_vars = try std.fmt.parseInt(usize, tokens.next().?, 10);
    //     num_clauses = try std.fmt.parseInt(usize, tokens.next().?, 10);
    // }

    // clauses.ensureTotalCapacity(num_clauses) catch unreachable;

    while (try reader.readUntilDelimiterOrEofAlloc(allocator, '\n', 1024)) |line| {
        if (line.len == 0 or line[0] == 'c' or line[0] == 'p') {
            continue;
        }

        const clause = try parseDimacsClauseLine(allocator, line);
        clauses.append(clause) catch unreachable;
    }

    return clauses;
}

fn parseDimacsClauseLine(allocator: std.mem.Allocator, line: []const u8) !std.ArrayList(i32) {
    var tokens = std.mem.tokenizeScalar(u8, line, ' ');
    var clause = std.ArrayList(i32).init(allocator);
    errdefer clause.deinit();

    while (tokens.next()) |token| {
        const lit = try std.fmt.parseInt(i32, token, 10);
        if (lit == 0) {
            break;
        }

        clause.append(lit) catch unreachable;
    }

    return clause;
}

test "parseDimacsClauseLine" {
    {
        const clause = try parseDimacsClauseLine(std.testing.allocator, "1 2 3 20 -1337 0");
        defer std.testing.allocator.free(clause);

        try std.testing.expectEqualSlices(i32, &[_]i32{ 1, 2, 3, 20, -1337 }, clause);
    }

    {
        const clause = try parseDimacsClauseLine(std.testing.allocator, "1337 -90 0");
        defer std.testing.allocator.free(clause);

        try std.testing.expectEqualSlices(i32, &[_]i32{ 1337, -90 }, clause);
    }

    {
        const clause = try parseDimacsClauseLine(std.testing.allocator, "0 0 0");
        defer std.testing.allocator.free(clause);

        try std.testing.expectEqualSlices(i32, &[_]i32{}, clause);
    }
}
