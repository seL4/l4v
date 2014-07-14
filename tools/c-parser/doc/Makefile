#
# Copyright 2014, NICTA
#
# This software may be distributed and modified according to the terms of
# the BSD 2-Clause license. Note that NO WARRANTY is provided.
# See "LICENSE_BSD2.txt" for details.
#
# @TAG(NICTA_BSD)
#

ctranslation.pdf: ctranslation.tex
	pdflatex $< && bibtex ${<:.tex=.aux} && pdflatex $< && pdflatex $<

.PHONY: clean distclean
clean:
	-/bin/rm -f ctranslation.{aux,bbl,blg,log,toc}

distclean: clean
	-/bin/rm -f ctranslation.pdf
