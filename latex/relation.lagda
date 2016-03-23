\documentclass{article}

\usepackage{xltxtra}

\usepackage{amsmath,amsthm,thmtools}
\declaretheorem[name=Theorem]{theorem}
\declaretheorem[name=Lemma]{lemma}
\usepackage{agda}

%\usepackage[language=english,eprint=false,doi=false]{biblatex}
%\addbibresource[location=remote]{http://www.citeulike.org/bibtex/user/miguelpagano/library?fieldmap=posted-at:posted-date&clean_urls=0}

\usepackage{tikz}
\usetikzlibrary{arrows}%,decorations.pathmorphing}

\usepackage{subfig}
%\title{A formalisation of Church-Rosser using parallel reductions}

\newcommand{\pred}{\Rightarrow}
\newcommand{\reduction}{\rightarrow}
\newcommand{\reduces}[2]{#1\,\rightarrow\,#2}
\newcommand{\reducesn}[2]{#1\,\rightarrow^{n}\,#2}
\newcommand{\transclos}[1]{#1^\ast}
\begin{document}
%\maketitle

\input{../Relation.lagda}

%\printbibliography

\end{document}
