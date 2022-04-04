package game;

import tabular.Tabular;

import java.util.Iterator;

public class Game {
    private PlayerResultNode head;
    private int size = 0;

    public int getSize() {
        return size;
    }

    public boolean addPlayer(String name) {
        PlayerResult newStudent = new PlayerResult(name);
        return insertSorted(newStudent);
    }

    public PlayerResult getResultByIndex(int idx) {
        PlayerResultNode cur = head;
        while (cur != null && idx > 0) {
            cur = cur.next;
            idx--;
        }
        if (cur != null) {
            return cur.player;
        }
        return null;
    }

    public PlayerResult getResultByPlayerName(String name) {
        PlayerResultNode cur = head;
        while (cur != null && cur.player.getName().compareTo(name) < 0) {
            cur = cur.next;
        }
        if (cur != null && cur.player.getName().equals(name)) {
            return cur.player;
        }
        return null;
    }

    public boolean setPoints(String name, int category, int points) {
        PlayerResult player = getResultByPlayerName(name);
        if (player != null) {
            return player.setPoints(category, points);
        } else {
            return false;
        }
    }

    // TODO Tabular getScoreSheet() --------------------------------------------------------------

    // TODO private inner class ScoreSheet ----------------------------------------

    // TODO static inner class PlayerResultNode ------------------------------------------------

    public Tabular getScoreSheet() {
        return new ScoreSheet();
    }

    private static class PlayerResultNode {
        PlayerResult player;
        PlayerResultNode next;

        public PlayerResultNode(PlayerResult st) {
            player = st;
        }
    }

    // Rows are players, columns are categories, values are points.
    private class ScoreSheet implements Tabular {
        @Override
        public int rowCount() {
            return getSize();
        }

        @Override
        public int colCount() {
            return PlayerResult.N_CATEGORIES;
        }

        @Override
        public String rowName(int row) {
            return "Player " + getResultByIndex(row).getName();
        }

        @Override
        public String colName(int col) {
            return "Category " + col;
        }

        @Override
        public Iterable<Integer> iterableRow(int row) {
            return () -> new Iterator<>() {
                int index = 0;

                @Override
                public boolean hasNext() {
                    return index < colCount();
                }

                @Override
                public Integer next() {
                    return getResultByIndex(row).getPoints(index++);
                }
            };
        }

        @Override
        public Iterable<Integer> iterableCol(int col) {
            return () -> new Iterator<>() {
                int index = 0;

                @Override
                public boolean hasNext() {
                    return index < rowCount();
                }

                @Override
                public Integer next() {
                    return getResultByIndex(index++).getPoints(col);
                }
            };
        }
    }

    // private section --------------------------------------------------------

    private boolean insertSorted(PlayerResult newPlayer) {
        PlayerResultNode prev = null;
        PlayerResultNode curr = head;
        // sorted by studentId
        while (curr != null && curr.player.getName().compareTo(newPlayer.getName()) < 0) {
            prev = curr;
            curr = curr.next;
        }
        if (curr == null || !curr.player.getName().equals(newPlayer.getName())) {
            // insert new student
            PlayerResultNode newNode = new PlayerResultNode(newPlayer);
            if (prev == null) {
                head = newNode;
                head.next = curr;
            } else {
                prev.next = newNode;
                newNode.next = curr;
            }
            size++;
            return true;
        } else {
            // already contained
            return false;
        }
    }

}



