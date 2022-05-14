package stackoverflow;


import com.google.gson.Gson;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.net.HttpURLConnection;
import java.net.MalformedURLException;
import java.net.ProtocolException;
import java.net.URL;
import java.util.*;
import java.util.function.Function;
import java.util.stream.Collectors;
import java.util.stream.Stream;
import java.util.zip.GZIPInputStream;

// These data classes do NOT contain all possible fields.
// The complete list of fields can be found at https://api.stackexchange.com/docs
public class Data {
    public static class User {
        private User() {

        }

        private long reputation;
        private long user_id;
        private String display_name;
        private String link;

        public long getReputation() {
            return reputation;
        }

        public long getUserId() {
            return user_id;
        }

        public String getDisplayName() {
            return display_name;
        }

        public String getLink() {
            return link;
        }

        @Override
        public boolean equals(Object o) {
            if (this == o) return true;
            if (o == null || getClass() != o.getClass()) return false;
            User user = (User) o;
            return Objects.equals(display_name, user.display_name);
        }

        @Override
        public int hashCode() {
            return Objects.hash(display_name);
        }

        @Override
        public String toString() {
            return "User{" +
                    "reputation=" + reputation +
                    ", user_id=" + user_id +
                    ", display_name='" + display_name + '\'' +
                    ", link='" + link + '\'' +
                    '}';
        }
    }

    public static class Question {
        private Question() {

        }

        private String[] tags;
        private User owner;
        private long view_count;
        /**
         * Is 0 if no answer is accepted
         */
        private long accepted_answer_id;
        private long score;

        private long favorite_count;
        /**
         * All dates in the API are in unix epoch time, which is the number of seconds since midnight UTC January 1st, 1970. The API does not accept or return fractional times, everything should be rounded to the nearest whole second.
         * See https://api.stackexchange.com/docs/dates
         */
        private long creation_date;
        private long question_id;
        private String link;
        private String title;

        private String body;

        private Answer[] answers;

        public String[] getTags() {
            return tags;
        }

        public User getOwner() {
            return owner;
        }

        public long getViewCount() {
            return view_count;
        }

        /**
         * @return The ID of the accepted answer, or 0 if no answer has been accepted.
         */
        public long getAcceptedAnswerId() {
            return accepted_answer_id;
        }

        public long getScore() {
            return score;
        }

        public long getFavoriteCount() {
            return favorite_count;
        }

        /**
         * All dates in the API are in unix epoch time, which is the number of seconds since midnight UTC January 1st, 1970. The API does not accept or return fractional times, everything should be rounded to the nearest whole second.
         * See https://api.stackexchange.com/docs/dates
         */
        public long getCreationDate() {
            return creation_date;
        }

        public long getQuestionId() {
            return question_id;
        }

        public String getLink() {
            return link;
        }

        public String getTitle() {
            return title;
        }

        public String getBody() {
            return body;
        }

        public Answer[] getAnswers() {
            return answers;
        }

        @Override
        public boolean equals(Object o) {
            if (this == o) return true;
            if (o == null || getClass() != o.getClass()) return false;
            Question question = (Question) o;
            return question_id == question.question_id;
        }

        @Override
        public int hashCode() {
            return Objects.hash(question_id);
        }

        @Override
        public String toString() {
            return "Question{" +
                    "title='" + title + '\'' +
                    ", tags=" + Arrays.toString(tags) +
                    ", owner=" + owner +
                    ", view_count=" + view_count +
                    ", accepted_answer_id=" + accepted_answer_id +
                    ", score=" + score +
                    ", favorite_count=" + favorite_count +
                    ", creation_date=" + creation_date +
                    ", question_id=" + question_id +
                    ", link='" + link + '\'' +
                    ", body='" + body.replace("\r", "").replace("\n", "") + '\'' +
                    ", answers=" + Arrays.toString(answers) +
                    '}';
        }
    }

    public class Answer {
        private Answer() {

        }

        private long answer_id;

        private String body;

        private long creation_date;

        private boolean is_accepted;

        private User owner;

        private int score;

        public long getAnswerId() {
            return answer_id;
        }

        public String getBody() {
            return body;
        }

        /**
         * All dates in the API are in unix epoch time, which is the number of seconds since midnight UTC January 1st, 1970. The API does not accept or return fractional times, everything should be rounded to the nearest whole second.
         * See https://api.stackexchange.com/docs/dates
         */
        public long getCreationDate() {
            return creation_date;
        }

        public boolean isAccepted() {
            return is_accepted;
        }

        public User getOwner() {
            return owner;
        }

        public int getScore() {
            return score;
        }

        @Override
        public boolean equals(Object o) {
            if (this == o) return true;
            if (o == null || getClass() != o.getClass()) return false;
            Answer answer = (Answer) o;
            return answer_id == answer.answer_id;
        }

        @Override
        public int hashCode() {
            return Objects.hash(answer_id);
        }

        @Override
        public String toString() {
            return "Answer{" +
                    "answer_id=" + answer_id +
                    ", body='" + body.replace("\r", "").replace("\n", "") + '\'' +
                    ", creation_date=" + creation_date +
                    ", is_accepted=" + is_accepted +
                    ", owner=" + owner +
                    ", score=" + score +
                    '}';
        }
    }

    private static String STACKOVERFLOW_API_URL = "https://api.stackexchange.com/2.3/";
    private static String TOP_100_KOTLIN_QUESTIONS_CONFIG = "questions?pagesize=100&order=desc&sort=votes&tagged=kotlin&site=stackoverflow&filter=!LJbtCzGtLcC-OE-.7b_A25";
    private static String RESOURCE_URL = STACKOVERFLOW_API_URL + TOP_100_KOTLIN_QUESTIONS_CONFIG;

    private Question[] items = new Question[0];

    private Data() {
    }

    /**
     * @return The loaded data, or null if an exception occurred
     */
    public static Data loadTop100FromWeb() {
        // HttpClient would be supported in Java 11, fall back to HttpURLConnection to ensure Java 8 compatibility
        try {
            URL url = new URL(RESOURCE_URL);
            HttpURLConnection con = (HttpURLConnection) url.openConnection();
            con.setRequestMethod("GET");
            // StackExchange pages use compression in HTTP access, default is GZIP
            // See: https://api.stackexchange.com/docs/compression
            con.setRequestProperty("Accept-Encoding", "gzip");

            BufferedReader reader = null;
            if ("gzip".equals(con.getContentEncoding())) {
                // As expected, data has been returned compressed
                reader = new BufferedReader(new InputStreamReader(new GZIPInputStream(con.getInputStream())));
            } else {
                // StackExchange should _never_ send uncompressed data
                // Still, why not have a fallback? :)
                reader = new BufferedReader(new InputStreamReader(con.getInputStream()));
            }

            // Use Gson library to convert JSON into Data.Question and Data.User objects
            Gson gson = new Gson();
            Data data = gson.fromJson(reader, Data.class);
            // Shuffle the response to make this exercise a bit more interesting ;)
            List<Question> itemList = Arrays.asList(data.items);
            Collections.shuffle(itemList);
            itemList.toArray(data.items);
            reader.close();

            return data;
        } catch (MalformedURLException ex) {
            System.err.println("Malformed URL: " + RESOURCE_URL);
            ex.printStackTrace();
        } catch (ProtocolException ex) {
            System.err.println("Protocol exception:");
            ex.printStackTrace();
        } catch (IOException ex) {
            System.err.println("IO exception:");
            ex.printStackTrace();
        }

        return new Data();
    }

    public Stream<Question> stream() {
        // Generate new Stream<Question> based on the array 'items'
        return items.length == 0 ? Stream.empty() : Arrays.stream(items);
    }

    // All following TODOs should be implemented using this.stream().... with a single chain of Stream operations.

    public Optional<Question> getOldestQuestion() {
        // Return the oldest question (i.e., the question with the smallest creation date)
        return this.stream().min(Comparator.comparing(Question::getCreationDate));
    }

    public Optional<Question> getQuestionWithMostAnswers() {
        // Return the question with the most answers
        return this.stream().max(Comparator.comparing((q) -> q.getAnswers().length));
    }


    public List<Question> getAllQuestionsThatContain(String search) {
        // Return the list of questions that contain the parameter 'search' in the title or the body
        return this.stream().filter((q) -> (
                q.getTitle().contains(search) || q.getBody().contains(search)
        )).toList();
    }

    public Optional<Question> getQuestionWithLongestAcceptedAnswer() {
        // Return the question with the longest answer body in its accepted answer (look at the isAccepted-flag of the question's answers)
        return this.stream()
                .filter((q) -> q.getAcceptedAnswerId() != 0)
                .max(Comparator.comparing((q) -> (
                        Arrays.stream(q.getAnswers())
                                .filter((qq) -> qq.getAnswerId() == q.getAcceptedAnswerId())
                                .findAny().orElseThrow().getBody().length()
                )));
    }

    public List<String> getDistinctQuestionOwnerNames() {
        // Return the distinct user names that asked questions
        return this.stream().map((q) -> q.getOwner().getDisplayName()).distinct().toList();
    }

    public long getDistinctAnswerOwnerCount() {
        // Return the number of unique users (user names) that answered questions
        return this.stream().flatMap((q) -> Arrays.stream(q.getAnswers()).map(Answer::getOwner))
                .distinct().count();
    }

    public List<Question> getQuestionsSortedDescendingByViewCount() {
        // Return all questions, sorted descending by view count
        return this.stream().sorted(Comparator.comparing(Question::getViewCount).reversed()).toList();
    }

    public List<Question> getQuestionsWithoutTag(String tag) {
        // Return a list of all question that are not tagged with tag 'tag'
        return this.stream().filter((q) -> !Arrays.asList(q.getTags()).contains(tag)).toList();
    }

    public OptionalDouble getAverageQuestionOwnerReputation() {
        // Return the average reputation of question owners using mapToLong() and average()
        return this.stream().mapToLong((q) -> q.getOwner().getReputation()).average();
    }

    public double getAverageQuestionScore() {
        // Return the average question score using collect() in conjunction with Collectors.averagingLong()
        return this.stream().collect(Collectors.averagingLong(Question::getScore));
    }

    public Map<Long, List<Question>> getQuestionsGroupedByFavouriteCount() {
        // Return questions grouped by their first word in the body (case insensitive, i.e., use toLowerCase() on the word/body)
        // (NOTE: Implemented according to method name/declaration (type) as opposed to the comment.
        return this.stream().collect(Collectors.groupingBy(Question::getFavoriteCount));
    }

    public Map<Boolean, List<Question>> getPartitionByAcceptedAnswer() {
        // Return all questions, partitioned by the fact if the question has an answer (true) or not (false)
        return this.stream().collect(Collectors.groupingBy((q) -> q.getAcceptedAnswerId() == 0));
    }

    public List<String> getTopAnswerers(int takeNTop) {
        // Return a list of user names in conjunction with their answer count (i.e., a list of Strings "<user_name> answered <answer_count> times")
        // Sort the users descending based on answer count, and only take the takeNTop users

        return this.stream().flatMap((q) -> Arrays.stream(q.getAnswers()))
                .collect(Collectors.groupingBy(Answer::getOwner))
                .entrySet().stream()
                // ghetto hack because .reverseOrder() doesn't work for some arcane reason
                .sorted(Comparator.comparing((e) -> -1 * e.getValue().size()))
                .limit(takeNTop)
                .map((e) -> (
                        String.format("%s answered %d", e.getKey().getDisplayName(), e.getValue().size()))
                ).toList();
    }

    @Override
    public String toString() {
        return "Data{" +
                "items=" + Arrays.toString(items) +
                '}';
    }
}
