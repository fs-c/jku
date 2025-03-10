const std = @import("std");
const Formula = @import("model.zig").Formula;
const Clause = @import("model.zig").Clause;

pub fn recursiveSolve(allocator: std.mem.Allocator, formula: *Formula, assignment: *std.ArrayList(i32)) bool {
    while (getFirstUnitClauseLiteral(formula)) |literal| {
        propagateBinaryConstraint(formula, literal);
        if (literal > 0) {
            assignment.append(literal) catch unreachable;
        }
    }

    if (formula.isEmpty()) {
        return true;
    }

    for (formula.clauses.items) |clause| {
        if (clause.isEmpty()) {
            return false;
        }
    }

    const literal = getFirstLiteral(formula).?;

    var clause = Clause(Formula.LiteralType).initFromLiterals(allocator, &[_]Formula.LiteralType{});
    errdefer clause.deinit();

    {
        clause.add(literal);
        formula.clauses.append(clause) catch unreachable;

        if (recursiveSolve(allocator, formula, assignment)) {
            return true;
        } else {
            _ = clause.remove(literal);
            _ = formula.clauses.pop();
        }
    }

    {
        clause.add(-literal);
        formula.clauses.append(clause) catch unreachable;

        if (recursiveSolve(allocator, formula, assignment)) {
            return true;
        } else {
            _ = clause.remove(-literal);
            _ = formula.clauses.pop();
        }
    }

    return false;
}

test recursiveSolve {
    {
        var assignment = std.ArrayList(i32).init(std.testing.allocator);
        defer assignment.deinit();

        var formula = Formula.initFromClauseSlices(std.testing.allocator, &[_][]const Formula.LiteralType{
            &[_]Formula.LiteralType{ 1, 2, 3, 4, 5 },
            &[_]Formula.LiteralType{-1},
            &[_]Formula.LiteralType{-2},
            &[_]Formula.LiteralType{3},
        });
        defer formula.deinit();

        try std.testing.expect(recursiveSolve(std.testing.allocator, &formula, &assignment));
        try std.testing.expectEqualSlices(i32, &[_]i32{3}, assignment.items);
    }

    {
        var assignment = std.ArrayList(i32).init(std.testing.allocator);
        defer assignment.deinit();

        var formula = Formula.initFromClauseSlices(std.testing.allocator, &[_][]const Formula.LiteralType{
            &[_]Formula.LiteralType{ -1, -2 },
            &[_]Formula.LiteralType{ -1, 2 },
            &[_]Formula.LiteralType{ 1, -2 },
            &[_]Formula.LiteralType{ 1, 2 },
        });
        defer formula.deinit();

        try std.testing.expect(!recursiveSolve(std.testing.allocator, &formula, &assignment));
    }
}
/// returns the literal which makes up the first unit clause in the formula
fn getFirstUnitClauseLiteral(formula: *Formula) ?Formula.LiteralType {
    for (formula.clauses.items) |clause| {
        if (clause.literals.count() == 1) {
            var it = clause.literals.keyIterator();
            return it.next().?.*;
        }
    }
    return null;
}

test getFirstUnitClauseLiteral {
    var formula_with_unit_clause = Formula.initFromClauseSlices(std.testing.allocator, &[_][]const Formula.LiteralType{
        &[_]Formula.LiteralType{ 1, -2, 3, 4 },
        &[_]Formula.LiteralType{2},
        &[_]Formula.LiteralType{ -1, -2, -3 },
    });
    defer formula_with_unit_clause.deinit();

    const literal = getFirstUnitClauseLiteral(&formula_with_unit_clause);
    try std.testing.expectEqual(2, literal);

    var formula_without_unit_clause = Formula.initFromClauseSlices(std.testing.allocator, &[_][]const Formula.LiteralType{
        &[_]Formula.LiteralType{ 1, -2, 3, 4 },
        &[_]Formula.LiteralType{ -1, -2, -3 },
    });
    defer formula_without_unit_clause.deinit();

    try std.testing.expect(getFirstUnitClauseLiteral(&formula_without_unit_clause) == null);
}

fn getFirstLiteral(formula: *Formula) ?Formula.LiteralType {
    for (formula.clauses.items) |clause| {
        if (!clause.isEmpty()) {
            var it = clause.literals.keyIterator();
            return it.next().?.*;
        }
    }
    return null;
}

test getFirstLiteral {
    var formula = Formula.initFromClauseSlices(std.testing.allocator, &[_][]const Formula.LiteralType{
        &[_]Formula.LiteralType{ 1, -2, 3, 4 },
        &[_]Formula.LiteralType{2},
        &[_]Formula.LiteralType{ -1, -2, -3 },
    });
    defer formula.deinit();

    try std.testing.expect(getFirstLiteral(&formula) != null);

    var empty_formula = Formula.initFromClauseSlices(std.testing.allocator, &[_][]const Formula.LiteralType{});
    defer empty_formula.deinit();

    try std.testing.expect(getFirstLiteral(&empty_formula) == null);
}

/// remove all clauses that contain the literal and remove all occurences of !literal
fn propagateBinaryConstraint(formula: *Formula, literal: Formula.LiteralType) void {
    // iterate backwards to avoid issues with index shifting, because we remove during iteration
    var i: usize = formula.clauses.items.len;
    while (i > 0) {
        i -= 1;
        var clause = &formula.clauses.items[i];

        if (clause.contains(literal)) {
            _ = formula.swapRemove(i);
        } else {
            _ = clause.remove(-literal);
        }
    }
}

test propagateBinaryConstraint {
    var formula = Formula.initFromClauseSlices(std.testing.allocator, &[_][]const Formula.LiteralType{
        &[_]Formula.LiteralType{ 1, 2, 3 },
        &[_]Formula.LiteralType{ -1, 2, 3, 4 },
        &[_]Formula.LiteralType{ 4, -5, -6 },
        &[_]Formula.LiteralType{1},
    });
    defer formula.deinit();

    propagateBinaryConstraint(&formula, 1);

    try std.testing.expect(formula.eqToSlice(&[_][]const Formula.LiteralType{
        &[_]Formula.LiteralType{ 2, 3, 4 },
        &[_]Formula.LiteralType{ 4, -5, -6 },
    }));
}
