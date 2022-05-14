package stackoverflow.main;

import inout.Out;
import stackoverflow.Data;

import java.util.Date;
import java.util.List;

public class Main {
    public static void main(String[] args) {
        System.out.println("Analysis of Top 100 questions (based on score) tagged with 'Kotlin'");
        System.out.println("==================================================");

        Data data = Data.loadTop100FromWeb();

        Out.println("\n3 random questions (stream().limit(3)):");
        data.stream().limit(3).forEach(Out::println);
        Out.println("\noldest question:");
        Out.println(data.getOldestQuestion().map(q -> String.format("\"%s\" on %s", q.getTitle(), new Date(q.getCreationDate() * 1000))).orElse("not available"));
        Out.println("\nquestion with most answers:");
        Out.println(data.getQuestionWithMostAnswers().map(q -> String.format("\"%s\" with %d answers", q.getTitle(), q.getAnswers().length)).orElse("not available"));
        Out.println("\nall questions that contain the word 'Stream':");
        data.getAllQuestionsThatContain("Stream").forEach(Out::println);
        Out.println("\nquestion with longest accepted answer body:");
        Out.println(data.getQuestionWithLongestAcceptedAnswer().map(Data.Question::getTitle).orElse("not available"));
        Out.println("\nnumber of distinct users that asked questions:");
        Out.println(data.getDistinctQuestionOwnerNames().size());
        Out.println("\nnumber of distinct users that answered questions:");
        Out.println(data.getDistinctAnswerOwnerCount());
        Out.println("\ntop three most viewed questions:");
        data.getQuestionsSortedDescendingByViewCount().stream().limit(3).map(q -> String.format("\"%s\" viewed %d times", q.getTitle(), q.getViewCount())).forEach(Out::println);
        Out.println("\nnumber of questions without the tag 'android':");
        Out.println(data.getQuestionsWithoutTag("android").size());
        Out.println("\naverage question owner reputation:");
        Out.println(data.getAverageQuestionOwnerReputation().orElse(-1));
        Out.println("\naverage question score:");
        Out.println(data.getAverageQuestionScore());
        Out.println("\ngroup questions by first body word:");
        data.getQuestionsGroupedByFavouriteCount().forEach((favouriteCount, questions) -> {
            Out.println(String.format("  %d times favourited - %d questions", favouriteCount, questions.size()));
        });
        Out.println("\npartition by accepted answer");
        List<Data.Question> answered = data.getPartitionByAcceptedAnswer().get(true);
        List<Data.Question> nonAnswered = data.getPartitionByAcceptedAnswer().get(false);
        Out.println(String.format("  answered: %d", answered.size()));
        Out.println(String.format("  non-answered: %d", nonAnswered.size()));
        Out.println("\ntop answerers");
        data.getTopAnswerers(5).forEach(answererText -> {
            Out.println(String.format("  %s", answererText));
        });
    }
}
