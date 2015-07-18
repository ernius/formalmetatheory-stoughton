# name of agda compiler name
#AGDA = agda2.4.2.2  
AGDA = agda

LATEX = pdflatex

# agda library location
#AGDALIBRARYFLAGS = -i . -i ~/Documents/NewAgda/agda-stdlib-0.9/src/
AGDALIBRARYFLAGS = -i . -i /usr/share/agda-stdlib/

# agda html
AGDAHTMLFLAGS = --html

# agda latex
AGDALATEXFLAGS = --latex

latex/%.tex : %.lagda
	$(AGDA) $(AGDALATEXFLAGS) $(AGDALIBRARYFLAGS) $<

#bib : latex/resumen.bib
#	cd latex; pdflatex resumen.tex; bibtex resumen;pdflatex resumen.tex;pdflatex resumen.tex; cd ..;

resumen : latex/resumen.tex latex/Substitution.tex latex/SubstitutionLemmas.tex latex/Term.tex latex/Alpha.tex
	cd latex; $(LATEX) resumen.tex

chi : latex/chi-nominal-pitts.tex latex/Chi.tex
	cd latex; $(LATEX) chi-nominal-pitts.tex

Substitution : Substitution.lagda
	$(AGDA) $(AGDALIBRARYFLAGS) Substitution.lagda

SubstitutionLemmas : SubstitutionLemmas.lagda
	$(AGDA) $(AGDALIBRARYFLAGS) SubstitutionLemmas.lagda

html : *.lagda
	$(AGDA) $(AGDAHTMLFLAGS) $(AGDALIBRARYFLAGS) SubstitutionLemmas.lagda; #cp -rf html/ ../gh-pages/formalmetatheory-nominal/

clean :
	rm *.agdai
