module ssw.psw2.examtable {
    requires transitive javafx.controls;
    requires transitive javafx.fxml;
    requires transitive javafx.base;
    requires transitive javafx.graphics;
    requires transitive java.sql;
    requires java.rmi;

    exports ssw.psw2.examtable.frontend;
    opens ssw.psw2.examtable.frontend to javafx.fxml;
    
    exports ssw.psw2.examtable.common;
    opens ssw.psw2.examtable.common to javafx.fxml;
}
