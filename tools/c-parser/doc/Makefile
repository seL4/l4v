#
# Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
#
# SPDX-License-Identifier: BSD-2-Clause
#

ctranslation.pdf: ctranslation.tex
	pdflatex $< && bibtex ${<:.tex=.aux} && pdflatex $< && pdflatex $<

.PHONY: clean distclean
clean:
	-/bin/rm -f ctranslation.{aux,bbl,blg,log,toc}

distclean: clean
	-/bin/rm -f ctranslation.pdf
