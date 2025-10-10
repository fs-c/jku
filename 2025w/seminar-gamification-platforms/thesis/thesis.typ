#set heading(numbering: "1")
#set list(indent: 0.5em)

#align(center, text(17pt)[
  *Gamification: Evaluation of Platforms*
])

#align(center, [
  Laurenz Weixlbaumer \
  K11804751\@students.jku.at
])

#align(center, block(width: 75%, [
  #set par(justify: true)
  #align(left, [*Abstract* #sym.space.quad #lorem(80)])
]))

#outline()

= Introduction

Provide background on gamification: Introductory definition, use cases, etc.

State the surveys goal/contribution and outline the structure of the thesis.

= Related Work

Others have done similar analyses before -- describe a selection of relevant prior art and outline commonalities/differences. (e.g. @MRGA15)

= Evaluation Criteria

Formally establish the process of the evaluation: Introduce a catalogue of criteria, ideally grouped into sub-categories ($->$ figure).

Justify the choice of criteria.

= Evaluation of Platforms

*(Main survey & analysis section.)*

Give rationale for selection of platforms/frameworks.

Describe the analysis. Likely more readable to not dedicate a paragraph to each framework but to instead go through the criteria one by one, synthesizing the respective results ($->$ table for per-framework results).

= Conclusion

Briefly restate introductory parts, summarize the findings.

Elaborate on unique features or lacks of particular systems.

= (Notes, relevant for 1st deliverable)

Literature reviews on gamification itself, i.e. not platforms/frameworks in particular:

- @Herz14 examines 37 studies to identify gamification requirements, but notes that much work has been done since then. In addition, the review was not the focus of the thesis. (Given)
- @HaKS14 examine 24 (empirical, peer-reviewed) studies, creating a framework to examine the effectiveness of gamification.

Literature reviews on (theoretical) frameworks for gamification:

- @MRGA15 identify 10 "framework features" and judge 18 papers describing gamification frameworks or generic gamification process descriptions accordingly. Their individual reasoning is not always given, but the feature groups appear promising for adoption. (Given)
- @MRGA17, from the same authers as above, follows a similar methodology, but considers more papers and has a stronger focus on education as opposed to industry applications.

Framework descriptions:

- Octalysis @Chou15
- 5W2H+M @CoGS19, although I couldn't really follow their description, and it doesn't appear to have gained any traction
- ...incomplete list, literature reviews contain many more

Actual implementations (conducted a GitHub search for "gamification"):

- gamification-engine#footnote([https://github.com/ActiDoo/gamification-engine]) (Given)
- Kinben#footnote([https://github.com/InteractiveSystemsGroup/GamificationEngine-Kinben, see also @KiKZ18]) (Given)
- UserInfuser#footnote([https://github.com/nlake44/UserInfuser]) (Given)
- laravel-gamify#footnote([https://github.com/qcod/laravel-gamify])
- level-up#footnote([https://github.com/cjmellor/level-up])
- django-gamification#footnote([https://github.com/mattjegan/django-gamification])
- yay#footnote([https://github.com/sveneisenschmidt/yay])
- hpi/gamification#footnote([https://github.com/hpi-schul-cloud/gamification])

Note that most of these are just relatively simple services exposing REST APIs for things like tracking points, badges, achievements, etc. and leave much of the actual gamification up to the user. Whereas most gamification frameworks described in the literature have a more holistic approach. This would make a comparison not very meaningful.

#bibliography(("references.yml", "references.bib"), style: "apa")
