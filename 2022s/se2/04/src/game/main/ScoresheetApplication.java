package game.main;

import game.Game;
import inout.Out;
import tabular.Tabular;

import static java.lang.String.format;

public class ScoresheetApplication {
    public static void main(String[] args) {
        Game game = new Game();

        addExampleData(game);

        Out.println();
        Out.println("-----------------------------------------------");
        Out.println("ScoresheetApplication: ");
        Out.println("-----------------------------------------------");

        Tabular pointsTable = game.getScoreSheet();

        int[] rowSums = pointsTable.rowSums();
        for (int i = 0; i < rowSums.length; i++) {
            Out.println(format("Sum of %s (row): %d", pointsTable.rowName(i), rowSums[i]));
        }
        Out.println();

        double[] colAverages = pointsTable.colAverages();
        for (int i = 0; i < colAverages.length; i++) {
            Out.println(format("Average of %s (column): %.1f", pointsTable.colName(i), colAverages[i]));
        }
        Out.println();

        Out.println(format("Overall category average: %.1f", pointsTable.average()));
    }

    private static void addExampleData(Game list) {
        list.addPlayer("Antonia");
        list.addPlayer("Franz");
        list.addPlayer("Birgit");
        list.addPlayer("Anna");
        list.addPlayer("Valentina");
        list.addPlayer("Basti");
        list.addPlayer("Gabe");
        list.addPlayer("Pepe");
        list.addPlayer("Pikachu");
        list.addPlayer("Fritz");

        list.setPoints("Antonia", 0, 8);
        list.setPoints("Antonia", 1, 9);
        list.setPoints("Antonia", 2, 17);
        list.setPoints("Antonia", 3, 10);
        list.setPoints("Antonia", 4, 7);
        list.setPoints("Antonia", 5, 9);

        list.setPoints("Franz", 0, 4);
        list.setPoints("Franz", 1, 0);
        list.setPoints("Franz", 2, 16);
        list.setPoints("Franz", 3, 6);
        list.setPoints("Franz", 4, 2);
        list.setPoints("Franz", 5, 4);

        list.setPoints("Birgit", 0, 9);
        list.setPoints("Birgit", 1, 5);
        list.setPoints("Birgit", 2, 16);
        list.setPoints("Birgit", 3, 7);
        list.setPoints("Birgit", 4, 8);
        list.setPoints("Birgit", 5, 8);

        list.setPoints("Anna", 0, 5);
        list.setPoints("Anna", 1, 6);
        list.setPoints("Anna", 2, 17);
        list.setPoints("Anna", 3, 0);
        list.setPoints("Anna", 4, 8);
        list.setPoints("Anna", 5, 8);

        list.setPoints("Valentina", 0, 7);
        list.setPoints("Valentina", 1, 8);
        list.setPoints("Valentina", 2, 15);
        list.setPoints("Valentina", 3, 6);
        list.setPoints("Valentina", 4, 3);
        list.setPoints("Valentina", 5, 9);

        list.setPoints("Basti", 0, 7);
        list.setPoints("Basti", 1, 6);
        list.setPoints("Basti", 2, 18);
        list.setPoints("Basti", 3, 9);
        list.setPoints("Basti", 4, 10);
        list.setPoints("Basti", 5, 9);

        list.setPoints("Gabe", 0, 5);
        list.setPoints("Gabe", 1, 1);
        list.setPoints("Gabe", 2, 14);
        list.setPoints("Gabe", 3, 5);
        list.setPoints("Gabe", 4, 7);
        list.setPoints("Gabe", 5, 6);

        list.setPoints("Pepe", 0, 10);
        list.setPoints("Pepe", 1, 10);
        list.setPoints("Pepe", 2, 10);
        list.setPoints("Pepe", 3, 10);
        list.setPoints("Pepe", 4, 9);
        list.setPoints("Pepe", 5, 10);

        list.setPoints("Pikachu", 0, 8);
        list.setPoints("Pikachu", 1, 9);
        list.setPoints("Pikachu", 2, 17);
        list.setPoints("Pikachu", 3, 10);
        list.setPoints("Pikachu", 4, 7);
        list.setPoints("Pikachu", 5, 9);

        list.setPoints("Fritz", 0, 3);
        list.setPoints("Fritz", 1, 3);
        list.setPoints("Fritz", 2, 14);
        list.setPoints("Fritz", 3, 2);
        list.setPoints("Fritz", 4, 9);
        list.setPoints("Fritz", 5, 10);
    }
}
