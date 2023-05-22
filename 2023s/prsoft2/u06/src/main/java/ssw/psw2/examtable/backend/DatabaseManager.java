package ssw.psw2.examtable.backend;

import java.sql.Connection;
import java.sql.DriverManager;
import java.sql.PreparedStatement;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.sql.SQLIntegrityConstraintViolationException;
import java.sql.Statement;
import java.util.ArrayList;
import java.util.List;

import ssw.psw2.examtable.common.Result;
import ssw.psw2.examtable.common.Student;

public class DatabaseManager {
	private static final String DB_URL = "jdbc:derby:resultsDB;create=true";

	private static final String EXAM_TABLE_NAME = "examtable";
	private static final String STUDENT_ID_ID = "result_studentID";
	private static final String STUDENT_NAME_ID = "result_studentName";
	private static final String STUDENT_FIRST_ID = "result_studentFirst";
	private static final String POINTS_ID = "result_points";

	private static final String IMPORT_QUERY = "SELECT * from " + EXAM_TABLE_NAME;
	private static final String GET_RESULT = IMPORT_QUERY + " WHERE " + STUDENT_ID_ID + "=?";
	private static final int GET_RESULT_STUDENT_ID = 1;

	private static final String UPDATE_PROPERTY = "UPDATE " + EXAM_TABLE_NAME + " SET %s=? WHERE " + STUDENT_ID_ID
			+ "=?";
	private static final int UPDATE_PARAM_NEW_VALUE = 1;
	private static final int UPDATE_PARAM_ELEMENT_ID = 2;

	private static final String INSERT = "INSERT INTO " + EXAM_TABLE_NAME + " (" + STUDENT_ID_ID + "," + STUDENT_NAME_ID
			+ ", " + STUDENT_FIRST_ID + ", " + POINTS_ID + ") VALUES (?,?,?,?)";
	private static final int INSERT_RESULT_PARAM_STUDENT_ID = 1;
	private static final int INSERT_RESULT_PARAM_STUDENT_NAME = 2;
	private static final int INSERT_RESULT_PARAM_STUDENT_FIRST = 3;
	private static final int INSERT_RESULT_PARAM_POINTS = 4;

	private static final String DELETE = "DELETE FROM " + EXAM_TABLE_NAME + " WHERE " + STUDENT_ID_ID + " = ?";
	private static final int DELETE_PARAM_ID = 1;

	private Connection dbConnection;

	public DatabaseManager() {
		dbConnection = null;
	}

	public void openConnection(boolean newDb) {
		if (dbConnection != null) {
			throw new IllegalStateException("Previous connection is still open");
		}

		try {
			dbConnection = DriverManager.getConnection(DB_URL);
		} catch (SQLException e) {
			throw new RuntimeException("Could not open database", e);
		}

		if (newDb) {
			deleteTables();
			createTables();
		}

		// ensure the database scheme is properly set up
		setupTables();
	}

	public void closeConnection() {
		if (dbConnection == null) {
			throw new IllegalStateException("Connection was already closed");
		}

		try {
			dbConnection.close();
		} catch (SQLException e) {
			throw new RuntimeException("Could not close database", e);
		}
	}

	protected void finalize() {
		closeConnection();
	}

	private void deleteTables() {
		try (Statement statement = dbConnection.createStatement()) {
			statement.execute(String.format("DROP TABLE %s", EXAM_TABLE_NAME));
		} catch (SQLException e) {
			e.printStackTrace();
		}
	}

	private void createTables() {
		try (Statement statement = dbConnection.createStatement()) {
			StringBuilder createStatement = new StringBuilder(
					String.format("CREATE TABLE %s (" + "%s VARCHAR(10) PRIMARY KEY, " + // student ID
							"%s VARCHAR(30), " + // student name
							"%s VARCHAR(20), " + // student first name
							"%s INTEGER)", // points
							EXAM_TABLE_NAME, STUDENT_ID_ID, STUDENT_NAME_ID, STUDENT_FIRST_ID, POINTS_ID));

			statement.execute(createStatement.toString());
		} catch (SQLException e) {
			throw new RuntimeException("Failed to create table: " + EXAM_TABLE_NAME, e);
		}
	}

	private void setupTables() {
		try (ResultSet dbTables = dbConnection.getMetaData().getTables(null, null, null, null)) {
			while (dbTables.next()) {
				final String tableName = dbTables.getString("TABLE_NAME");
				if (EXAM_TABLE_NAME.equalsIgnoreCase(tableName)) {

					// the table is already setup
					return;
				}
			}
		} catch (SQLException e) {
			throw new RuntimeException("Could not read available tables", e);
		}

		createTables();
	}

	public void insertResult(Result r) throws IllegalArgumentException {
		if (dbConnection == null) {
			throw new IllegalStateException("Connection already closed");
		}

		Student s = r.getStudent();

		try (PreparedStatement insertStatement = dbConnection.prepareStatement(INSERT)) {

			insertStatement.setString(INSERT_RESULT_PARAM_STUDENT_ID, s.getId());
			insertStatement.setString(INSERT_RESULT_PARAM_STUDENT_NAME, s.getName());
			insertStatement.setString(INSERT_RESULT_PARAM_STUDENT_FIRST, s.getFirstName());
			insertStatement.setInt(INSERT_RESULT_PARAM_POINTS, r.getPoints());

			final int affectedRows = insertStatement.executeUpdate();
			if (affectedRows != 1) {
				throw new RuntimeException("Failed to add new result to database");
			}
		} catch (SQLIntegrityConstraintViolationException e) {
			throw new IllegalArgumentException("Duplicate key!");
		} catch (SQLException e) {
			throw new RuntimeException("Could not insert new result into " + EXAM_TABLE_NAME, e);
		}
	}

	public void removeResult(String studentID) {
		if (dbConnection == null) {
			throw new IllegalStateException("Connection was already closed");
		}

		try (final PreparedStatement deleteStatement = dbConnection.prepareStatement(DELETE)) {
			deleteStatement.setString(DELETE_PARAM_ID, studentID);
			final int affectedRows = deleteStatement.executeUpdate();
			if (affectedRows != 1) {
				throw new RuntimeException("Deletion affected an unexpected number of rows: " + affectedRows);
			}
		} catch (SQLException e) {
			throw new RuntimeException("Could not delete result!", e);
		}
	}

	public void updateResult(String studentID, int newPoints) {
		if (dbConnection == null) {
			throw new IllegalStateException("Connection already closed");
		}

		try (final PreparedStatement updateStatement = dbConnection
				.prepareStatement(String.format(UPDATE_PROPERTY, POINTS_ID))) {
			updateStatement.setInt(UPDATE_PARAM_NEW_VALUE, newPoints);
			updateStatement.setString(UPDATE_PARAM_ELEMENT_ID, studentID);
			updateStatement.executeUpdate();
		} catch (SQLException e) {
			throw new RuntimeException("Failed to update property of " + studentID, e);
		}
	}

	public Result getResult(String studentID) {
		if (dbConnection == null) {
			throw new IllegalStateException("Connection was already closed");
		}

		try {
			try (PreparedStatement resultsQuery = dbConnection.prepareStatement(GET_RESULT)) {
				resultsQuery.setString(GET_RESULT_STUDENT_ID, studentID);
				try (final ResultSet items = resultsQuery.executeQuery()) {
					while (items.next()) {
						final Student s = new Student(items.getString(STUDENT_ID_ID), items.getString(STUDENT_NAME_ID),
								items.getString(STUDENT_FIRST_ID));
						final Result r = new Result(s);
						r.setPoints(items.getInt(POINTS_ID));
						return r;
					}
				}
			}
		} catch (SQLException e) {
			throw new RuntimeException("Failed to get result of student with id=" + studentID, e);
		}

		return null;
	}

	public List<Result> importResults() {
		if (dbConnection == null) {
			throw new IllegalStateException("Connection was already closed");
		}

		final List<Result> imported = new ArrayList<>();

		try {
			try (PreparedStatement resultsQuery = dbConnection.prepareStatement(IMPORT_QUERY)) {
				try (final ResultSet items = resultsQuery.executeQuery()) {
					while (items.next()) {
						final Student s = new Student(items.getString(STUDENT_ID_ID), items.getString(STUDENT_NAME_ID),
								items.getString(STUDENT_FIRST_ID));
						final Result r = new Result(s);
						r.setPoints(items.getInt(POINTS_ID));

						imported.add(r);
					}
				}
			}
		} catch (SQLException e) {
			throw new RuntimeException("Failed to import from database", e);
		}

		return imported;
	}

}
