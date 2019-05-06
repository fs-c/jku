final class Point {
	int x, y;

	Point(int x, int y) {
		this.x = x;
		this.y = y;
	}

	void move(int dx, int dy) {
		x += dx;
		y += dy;
	}
}

abstract class Shape {
	Point position;

	Shape(Point position) {
		this.position = position;
	}

	void move(int dx, int dy) {
		position.move(dx, dy);
	}

	abstract void draw();

	abstract boolean hit(Point point);
}

final class Circle extends Shape {
	int radius;

	Circle(Point pos, int radius) {
		super(pos);

		this.radius = radius;
	}

	void draw() {
		Window.drawCircle(position.x, position.y, radius);
	}

	boolean hit(Point point) {
		double distance = Math.sqrt(
			Math.pow(Math.abs(point.x - position.x), 2) +
			Math.pow(Math.abs(point.y - position.y), 2)
		);

		return distance < radius;
	}
}

class Rectangle extends Shape {
	int width, height;

	Rectangle(Point pos, int width, int height) {
		super(pos);

		this.width = width;
		this.height = height;
	}

	void draw() {
		Window.drawRectangle(position.x, position.y, width, height);
	}

	boolean hit(Point point) {
		int x = position.x + width;
		int y = position.y + height;

		return point.x > position.x && point.x < x &&
			point.y > position.y && point.y < y;
	}
}

class Square extends Rectangle {
	Square(Point pos, int width) {
		super(pos, width, width);
	}
}

class Group extends Shape {
	Shape[] shapes;

	Group(Point pos, Shape[] shapes) {
		super(pos);

		for (int i = 0; i < shapes.length; i++) {
			shapes[i].position.x += pos.x;
			shapes[i].position.y += pos.y;
		}

		this.shapes = shapes;
	}

	void draw() {
		for (Shape shape : shapes) {
			if (shape == null)
				continue;
			
			shape.draw();
		}
	}

	boolean hit(Point point) {
		for (Shape shape : shapes) {
			if (shape == null)
				continue;
			
			if (shape.hit(point))
				return true;
		}

		return false;
	}

	@Override
	void move(int dx, int dy) {
		for (Shape shape : shapes) {
			if (shape == null)
				continue;
			
			shape.move(dx, dy);
		}

		position.move(dx, dy);
	}
}