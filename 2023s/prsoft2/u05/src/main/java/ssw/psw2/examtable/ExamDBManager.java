package ssw.psw2.examtable;

import ssw.psw2.examtable.model.Result;
import ssw.psw2.examtable.model.Student;

import java.sql.*;
import java.util.ArrayList;
import java.util.List;

public class ExamDBManager {
    private static final String DB_URL = "jdbc:derby:examDB;create=true";
    private static final String RESULTS_TABLE_NAME = "Results";
    private static final String RESULT_ID = "id";
    private static final String RESULT_FIRST_NAME = "first_name";
    private static final String RESULT_LAST_NAME = "last_name";
    public static final String RESULT_POINTS = "points";

    private Connection db = null;

    public void openConnection() {
        if (db != null) {
            return;
        }

        try {
            db = DriverManager.getConnection(DB_URL);
        } catch (SQLException e) {
            System.err.println("failed opening connection to " + DB_URL);

            e.printStackTrace();
        }

        createTableIfNotExists();
    }

    public void closeConnection() {
        if (db == null) {
            return;
        }

        try {
            db.close();
        } catch (SQLException e) {
            e.printStackTrace();
        }
    }

    public void createTableIfNotExists() {
        // apache derby does not support 'create table if not exists' so we manually check the list of tables
        try (var result = db.getMetaData().getTables(null, null, RESULTS_TABLE_NAME.toUpperCase(), null)) {
            if (result.next()) {
                return;
            }
        } catch (SQLException e) {
            System.err.format("couldn't check if table %s already exists, continuing\n", RESULTS_TABLE_NAME);

            e.printStackTrace();
        }

        try (var s = db.createStatement()) {
            s.execute(String.format("create table %s ("
                    + "%s varchar(9) primary key,"
                    + "%s varchar(30) not null,"
                    + "%s varchar(30) not null,"
                    + "%s int"
                    + ")",
                    RESULTS_TABLE_NAME, RESULT_ID, RESULT_FIRST_NAME, RESULT_LAST_NAME, RESULT_POINTS));

            System.out.println("created table");
        } catch (SQLException e) {
            System.err.println("failed creating table " + RESULTS_TABLE_NAME);

            e.printStackTrace();
        }
    }

    public void addResult(String id, String firstName, String lastName, int points) {
        var insertString = String.format("insert into %s (%s, %s, %s, %s) values (?, ?, ?, ?)",
                RESULTS_TABLE_NAME, RESULT_ID, RESULT_FIRST_NAME, RESULT_LAST_NAME, RESULT_POINTS);

        try (var s = db.prepareStatement(insertString, Statement.RETURN_GENERATED_KEYS)) {
            // "hardcoding" the indices here because the statement string is right here anyway
            s.setString(1, id);
            s.setString(2, firstName);
            s.setString(3, lastName);
            s.setInt(4, points);

            if (s.executeUpdate() != 1) {
                System.err.println("add result didn't affect exactly one row");
            }
        } catch (SQLException e) {
            System.err.format("failed to add person, insert statement '%s'\n", insertString);

            e.printStackTrace();
        }
    }

    public void updateColumn(String id, String column, String value) {
        var updateString = String.format("update %s set %s = ? where %s = ?", RESULTS_TABLE_NAME, column, RESULT_ID);

        try (var s = db.prepareStatement(updateString, Statement.RETURN_GENERATED_KEYS)) {
            s.setString(1, value);
            s.setString(2, id);

            s.executeUpdate();
        } catch (SQLException e) {
            System.err.format("failed to update column, update statement '%s'\n", updateString);

            e.printStackTrace();
        }
    }

    public void removeResult(String id) {
        var removeString = String.format("delete from %s where %s = ?", RESULTS_TABLE_NAME, RESULT_ID);

        try (var s = db.prepareStatement(removeString, Statement.RETURN_GENERATED_KEYS)) {
            s.setString(1, id);

            s.executeUpdate();
        } catch (SQLException e) {
            System.err.println("failed to remove result " + id);

            e.printStackTrace();
        }
    }

    public List<Result> getResults() {
        List<Result> results = new ArrayList<>();

        try (Statement s = db.createStatement()) {
            var selectString = String.format("select * from %s", RESULTS_TABLE_NAME);

            try (var row = s.executeQuery(selectString)) {
                while (row.next()) {
                    var result = new Result(new Student(row.getString(RESULT_ID), row.getString(RESULT_FIRST_NAME), row.getString(RESULT_LAST_NAME)));

                    result.setPoints(row.getInt(RESULT_POINTS));

                    results.add(result);
                }
            }
        } catch (SQLException e) {
            System.err.println("failed to get results");

            e.printStackTrace();
        }

        return results;
    }
}
