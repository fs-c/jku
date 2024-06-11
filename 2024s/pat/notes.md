wir werden ueber Agile Methodologies in the Engineering of Cyber-Physical Systems sprechen

## next Inhaltsueberblick

dahingehend ein kleiner inhaltsueberblick:

einleitend werden wir unsere forschungsfrage konkretisieren und "agile" definieren

dann werden wir zwei agile methoden genauer im kontext von cps untersuchen

abschliessend werden wir ein kurzes fazit ziehen, und einige gedanken fuer die zukunft (in diesem kontext) teilen

## next Einleitung

welche agile methoden werden !im kontext von cps! verwendet
was sind die auswirkungen

    wir werden das ein wenig einschraenken, und uns zwei ausgewaehlte themen ansehen, dazu gleich mehr

kurz ein paar worte zu agile im allgemeinen

    viele definitionen - name sagt vieles: man will agil sein, dh man will flexibel, anpassungsfaehig sein

    wird !einerseits! erreicht durch eine iterative arbeitsweise mit viel fokus auf strukturierte kommunikation

    !andererseits! grosses ziel, so schnell wie moeglich (ASAP) funktionierende software zu haben ("shippable" software)
    kann auch gleich getestet werden

    insbesondere zweck: verglichen zu traditionelleren methoden (zb wasserfall modell) bessere resilienz gegenueber aenderungen

        aenderungen im scope des projekts (neue/andere requirements etc)
        aenderungen in der teamkapazitaet (weniger/mehr devs, designer, etc)

        -> unter andeen eben weil flexiblere prioritisierung moeglich (iterationen), usw

agile, so wie wir es verstehen und eingefuehrt haben, geht auf eine handvoll informatiker zurueck (Manifesto for Agile Software Development, ca 2001)

agile praktiken im allgemeinen beschraenken sich aber natuerlich nicht nur auf informatik, bzw. reine software-projekte

    -> deswegen wollten wir uns agile im kontext von cps ansehen

## next Agile Methoden & CPS

jetzt wollen wir uns ein wenig spezialisieren bzw fokussieren

basis: aktuelles literature review (~~2 jahre alt) von agilen methoden in der entwicklung von cps

dieses lit review hat hauptsaechlich diese vier topics/themenbereiche identifiziert

    papers zu development frameworks
    papers zum unterricht von agile im kontext von cps
    papers zu requirements und testing
    papers zu continuous deployment

umfang ueberschaubar: development framework -> scrum

    scrum haben wir gewaehlt weil es das populaerste agile development framework ist

die themenbereiche continuous deployment und testing fassen wir zusammen zu continuous integration and delivery (abgekuerzt ci/cd)

die verwendung von diesen zwei agilen methoden im kontext von cps werden wir uns folgend genauer ansehen

## next Scrum

zuerst eine kurze einfuehrung in einen ueblichen scrum workflow

    kernbestandteil ist ein zyklus von sogenannten sprints (relativ kurz, ueblicherweise zwischen 2-4 wochen)

    in einem sprint wird an einem moeglichst fixen ticket-kontinent gearbeitet (also fixer scope pro sprint) das vor jedem sprint festegelegt wird

        output von einem sprint soll ein lauffaehiges und getestetes produkt-inkrement sein, in dem alle ziele des sprints umgesetzt sind

    taeglich gibt es eine moeglichst kurze besprechung (<15 minuten) in der teammitglieder ueber ihren fortschritt berichten

soviel zu scrum wie es vielleicht in einer puren software dev umgebung aussehen wuerde

## next Scrum & CPS

bei verwendung von scrum fuer cps development ist aber eine zentrale herausforderung, dass es mehr als ein team gibt: ueblicherweise mindestens software und hardware

ein zusammenlegen ist oft nicht sinvoll, weil diese teams oft voellig andere und wenig ueberschneidende spezialisierungen haben

ein loesungsansatz ist das sog "Scrum CPS"

    zwei "Arten" von sprints: Design Sprints und Hardware Sprints

    software ist design, und wird immer in design sprints gebaut

        wir programmierer unterscheiden bei software gerne zwischen *design* (architektur, interface bzw api, etc) und *implementierung*, aber in diesem kontext anderes zu betrachten weil bei software *kein produktionsschritt*

    bei hardware ist unterscheidung klarer, design sprints fuer hardware design (CAD, hardware description languages, etc) und hardware sprints fuer prototyping und arbeit mit der tatsaechlichen physischen hardware

## next Scrum & CPS

hier ein diagramm des entsprechend modifizierten workflows, oben design sprint, unten hardware sprint

das inkrementale output von hardware design sprints soll zum testen von weiterer arbeit verwendet werden koennen

    somit koennen hardware und software inkremental gemeinsam wachsen

sobald ein hardware sprint abgeschlossen ist, kann die software auch schon auf echter hardware getestet werden

## next Scrum & CPS

soviel zu einem moeglichen loesungsansatz fuer das synchonisationsproblem

aber nicht alle organisationen brauchen einen agilen entwicklungszyklus (wie scrum)

    wenn der problembereich gut erkundet ist, wenig innovation notwendig ist, wenig bis keine aenderungen in den requirements absehbar sind, etc.

    -> wenig notwendigkeit fuer agilen zyklus

gleichzeitig ist es nicht immer moeglich, agile entwicklungszyklen umzusetzen

    insbesondere in domaenen in denen cps relevant sind, kann protyping und testen sehr teuer sein

    sicherheitsauflagen rund um nachvervolgbarkeit von requirements und implementierung, unveranderbarkeit von code nach zertifizierung etc, koennen einen iterativen prozess unmoeglich machen

    zb: ein case-study fall der uns untergekommen ist, baut die kontrollsysteme von kampfjets

        viele sicherheitsbedenken, sehr teuer in bau und betrieb, etc.: nicht gut geeignet fuer agilen prozess

gleichzeitig zeigen case studies, dass organisationen deren domaene sonst keinen agilen zyklus zulassen wuerde bei notwendigkeit von agilitaet oftmals zu teilimplementationen tendieren

    es geht nicht um alles-oder-nichts
