class PolishCalculator {
	public static void main(String[] args) {
		Out.print("Command (R): ");
		char command = In.readChar();

		Out.print("Expression: ");
		String expression = In.readLine();


	}

	static boolean isOperator(char c) {
		return c == '+' || c == '-' || c == '*' || c == '/';
	}
}

class Expression {
	int value;
	char operation;

	Expression left, right;
}
