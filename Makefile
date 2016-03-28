# name of agda compiler name
AGDA = agda-2.4.2.5

LATEX = pdflatex

# agda library location
AGDALIBRARYFLAGS = -i . -i /home/ernius/Documents/NewAgda/agda-stdlib-0.11/src/

# agda html
AGDAHTMLFLAGS = --html

# agda latex
AGDALATEXFLAGS = --latex

latex/%.tex : %.lagda
	$(AGDA) $(AGDALATEXFLAGS) $(AGDALIBRARYFLAGS) $<

bib : latex/resumen.bib
      cd latex; pdflatex resumenCR.tex; bibtex resumenCR;pdflatex resumenCR.tex;pdflatex resumenCR.tex; cd ..;

resumen : latex/resumenChurchRosser.tex latex/ChurchRosser.tex latex/Substitution.tex latex/Alpha.tex latex/Chi.tex latex/Context.tex latex/ListProperties.tex latex/NaturalProp.tex latex/ParallelReduction.tex latex/SubstitutionLemmas.tex latex/Term.tex latex/Beta.tex
	cd latex; $(LATEX) resumenChurchRosser.tex; cd ..;	

ChurchRosser : ChurchRosser.lagda
	$(AGDA) $(AGDALIBRARYFLAGS) ChurchRosser.lagda

html : *.lagda
	$(AGDA) $(AGDAHTMLFLAGS) $(AGDALIBRARYFLAGS) ChurchRosser.lagda

clean :
	rm *.agdai
