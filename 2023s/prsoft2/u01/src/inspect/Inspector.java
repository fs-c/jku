package inspect;

import java.lang.reflect.*;
import java.util.*;
import java.util.stream.Collectors;

public class Inspector {
    // keeps track of current (head) and past objects, for navigation.
    // use Deque instead of Stack as per documentation recommendation
    private final Deque<Object> stack = new ArrayDeque<Object>();

    public Inspector(Object root) {
        if (root == null) {
            throw new IllegalArgumentException("root must not be null");
        }

        stack.push(root);
    }

    public void run() {
        var scanner = new Scanner(System.in);

        while (true) {
            try {
                var cur = stack.peek();

                printObject(cur);

                var input = scanner.nextLine().split(" ");

                switch (input[0]) {
                    case "i":
                        executeInspect(input, cur);
                        break;
                    case "b":
                        executeBack(stack);
                        break;
                    case "e":
                        executeEdit(input, cur, scanner);
                        break;
                    case "c":
                        executeCall(input, cur);
                        break;
                    case "q":
                        return;
                    default:
                        System.out.println("unrecognized command: " + input[0]);
                }
            } catch (NoSuchFieldException | IllegalAccessException | NoSuchMethodException | InvocationTargetException e) {
                System.out.println("error: " + e.toString());
            }
        }
    }

    private void printObject(Object obj) {
        var sb = new StringBuilder();
        var clazz = obj.getClass();

        sb.append('\n').append(clazz.getName()).append('\n');

        for (var field : getRelevantFields(clazz)) {
            var type = field.getType();

            sb.append("\tf ").append(type.getName()).append(' ').append(field.getName());

            if (type.isPrimitive() || type == String.class) {
                sb.append(": ");

                field.setAccessible(true);

                try {
                    sb.append(field.get(obj).toString());
                } catch (IllegalAccessException e) {
                    sb.append('[').append(e.getMessage()).append(']');
                }
            }

            sb.append('\n');
        }

        for (var method : getRelevantMethods(clazz)) {
            sb.append("\tm void ").append(method.getName())
                    .append('(')
                    .append(Arrays.stream(method.getParameterTypes())
                            .map(Class::toString).collect(Collectors.joining(", ")))
                    .append(')').append('\n');
        }

        System.out.println(sb);
    }

    private void executeInspect(String[] input, Object obj) throws NoSuchFieldException, IllegalAccessException {
        if (input.length < 2) {
            System.out.println("invalid arguments (i [field])");
            return;
        }

        var field = obj.getClass().getField(input[1]);

        if (field.isAnnotationPresent(InspectionBoundary.class)) {
            System.out.println("field is an inspection boundary, cannot inspect");

            return;
        }

        field.setAccessible(true);
        var value = field.get(obj);

        if (value == null) {
            System.out.println("field is null, cannot inspect");
        } else {
            stack.push(field.get(obj));
        }
    }

    private void executeBack(Deque<Object> stack) {
        if (stack.size() == 1) {
            System.out.println("no object to go back to");
        } else {
            stack.pop();
        }
    }

    private void executeEdit(String[] input, Object obj, Scanner scanner) throws NoSuchFieldException, IllegalAccessException {
        if (input.length < 3) {
            System.out.println("invalid arguments (e [field] [value])");
            return;
        }

        var field = Arrays.stream(getRelevantFields(obj.getClass()))
                .filter((f) -> f.getName().equals(input[1])).findFirst().orElse(null);

        if (field == null) {
            throw new NoSuchFieldException(input[1]);
        }

        var type = field.getType();

        if (!type.isPrimitive() && type != String.class) {
            System.out.println("can only edit primitives or Strings, type is " + type.getName());
            return;
        }

        if ((field.getModifiers() & Modifier.PRIVATE) != 0) {
            System.out.print("this field is private, confirm edit (y/n): ");

            var confirmation = scanner.nextLine();

            if (!confirmation.equals("y")) {
                return;
            }

            field.setAccessible(true);
        }

        field.set(obj, type == String.class ? input[2] : Integer.parseInt(input[2]));
    }

    private void executeCall(String[] input, Object cur) throws NoSuchMethodException, InvocationTargetException, IllegalAccessException {
        if (input.length < 2) {
            System.out.println("invalid arguments (c [method] [...params])");
            return;
        }

        // caveat: this does not handle overloads
        var method = Arrays.stream(getRelevantMethods(cur.getClass())).filter((m) -> m.getName().equals(input[1]))
                .findFirst().orElse(null);

        if (method == null) {
            throw new NoSuchMethodException(input[1]);
        }

        var paramCount = method.getParameterCount();

        // the index of the first (raw) call parameter in the input
        final var rawParamStart = 2;

        if ((input.length - paramCount) != rawParamStart) {
            System.out.println("invalid number of call parameters, expected " + paramCount);

            return;
        }

        var params = new Object[paramCount];
        // implementation detail: all types will be primitives or Strings
        var paramTypes = method.getParameterTypes();

        for (int i = 0; i < paramCount; i++) {
            var rawParam = input[rawParamStart + i];

            params[i] = paramTypes[i] == String.class ? rawParam : Integer.parseInt(rawParam);
        }

        method.invoke(cur, params);
    }

    // returns all fields relevant to the inspector: public and private fields of the given class and its superclasses
    private Field[] getRelevantFields(Class<?> clazz) {
        var fields = new ArrayList<Field>();

        do {
            var localFields = clazz.getDeclaredFields();

            fields.addAll(Arrays.asList(localFields));
        } while ((clazz = clazz.getSuperclass()) != Object.class);

        return fields.toArray(new Field[0]);
    }

    // returns all methods relevant to the inspector: public, return type void and only primitive/String parameters
    private Method[] getRelevantMethods(Class<?> clazz) {
        var methods = new ArrayList<Method>();

        for (var method : clazz.getDeclaredMethods()) {
            var returnType = method.getReturnType();
            var isPublic = (method.getModifiers() & Modifier.PUBLIC) != 0;
            var parameterTypes = method.getParameterTypes();

            if (returnType != void.class || !isPublic || Arrays.stream(parameterTypes).anyMatch((p) -> !p.isPrimitive())) {
                continue;
            }

            methods.add(method);
        }

        return methods.toArray(new Method[0]);
    }
}
