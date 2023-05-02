module ssw.psw2.examtable {
    requires transitive javafx.controls;
    requires transitive javafx.fxml;
    requires transitive javafx.base;
    requires transitive javafx.graphics;
    requires transitive java.sql;

    exports ssw.psw2.examtable;
    opens ssw.psw2.examtable to javafx.fxml;
    
    exports ssw.psw2.examtable.model;
    opens ssw.psw2.examtable.model to javafx.fxml;
}
