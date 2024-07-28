#***********************************************************
#
#  Makefile pour les modules de LatMRG (XDS)
#
#  Auteur: Richard Simard
#  Modifie le 2 mars 1999
#
#***********************************************************

#======================== REMARQUES =========================

# Note:
# L'utilisateur qui ne veut pas reconstruire les bibliotheques 
# peut eliminer tout ce qui suit la ligne  
#        ========== BILIOTHEQUE =========
# a la fin de ce fichier, de meme que toutes les references
# `a la cible lib.





#======================== DEFINITIONS =========================

SHELL = /bin/sh

MODULES1 = LILR      LISI      SILR      SISI

MODULES2 = BASIS     MULT      CONVERT

MODULES4 = BASISLR   BASISSI   MULTLI    MULTSI 

MODULES3 = BASISLR   BASISSI   MULTLI    MULTSI   \
           CONFIG    PRIM      LATBASIS  LATIO    \
           REDBAS    REDBAS2   REDBAS3   MRG      \
           PALPHA    TESTCONF  LATMRG    NORM  


DEF1 := $(addsuffix .def, ${MODULES1})
DEF3 := $(addsuffix .def, ${MODULES3})
DEF4 := $(addsuffix .def, ${MODULES4})

TEX1 := $(addsuffix .tex, ${MODULES1})
TEX3 := $(addsuffix .tex, ${MODULES3})

OBJ2 := $(addsuffix .o, ${MODULES2})
OBJ3 := $(addsuffix .o, ${MODULES3})

SYM2 := $(addsuffix .sym, ${MODULES2})
SYM3 := $(addsuffix .sym, ${MODULES3})

HHH2 := $(addsuffix .h, ${MODULES2})
HHH3 := $(addsuffix .h, ${MODULES3})

PROGLILR := coeff  latl  seekl  palpha
PROGSILR := latsr seeksr
PROGSISI := lats  seeks  maketab  menumrg  streams  maxper

LOOK1 = '-LOOKUP = latsr|seeksr|coeff|latl|seekl|palpha|lats|seeks|maketab|menumrg|streams|maxper|select = $(MACHINE)'

BIBLIO := "-biblio:=-lsentiers -lsimod -lmylib"

TCODE := $(XDSLIB)/tcode

VPATH = ${MACHINE}

DBG = optim


#======================== REGLES ==========================

#   eliminer tous les suffixes par defaut;  make sera plus rapide
.SUFFIXES:


#   *.tex ne dependent de rien;   make sera plus rapide
%.tex : ;
%.mod : ;

%.def : %.tex
	${TCODE} $< $@




#======================== CIBLES ==========================

modules: ${DEF3}
	@ echo "==================================================="
	@ echo "Compilation des modules de latmrg"
	xm =project Latmrg.prj
	@ echo "Compilation terminee."
	@ echo "==================================================="

select: ${DEF1} ${DEF4} select.mod
	xm =m select.mod $(LOOK1) ${BIBLIO}

modlilr: touch1  ${DEF1} ${DEF4} 
	$(MACHINE)/select li lr
	$(MAKE) modules LILR=lilr

modsilr: touch2  ${DEF1} ${DEF4} 
	$(MACHINE)/select si lr
	$(MAKE) modules LILR=silr

modsisi: touch3  ${DEF1} ${DEF4} 
	$(MACHINE)/select si si
	$(MAKE) modules LILR=sisi

touch1 touch2 touch3:
	touch ${TEX1} ${TEX3}

force all: clean select alllilr allsilr allsisi

alllilr:  modlilr
	$(MAKE) lib pglilr LILR=lilr

allsilr:  modsilr
	$(MAKE) lib pgsilr LILR=silr

allsisi:  modsisi
	$(MAKE) lib pgsisi LILR=sisi

proglilr:
	${MAKE} pglilr LILR=lilr
pglilr:
	cd dirlilr;   xm =m latl.mod -lilr=lilr -dbg=$(DBG)
	mv dirlilr/latl ${MACHINE}
	cd dirlilr;   xm =m seekl.mod -lilr=lilr -dbg=$(DBG)
	mv dirlilr/seekl ${MACHINE}
	cd dirlilr;   xm =m coeff.mod -lilr=lilr -dbg=$(DBG)
	mv dirlilr/coeff ${MACHINE}
	cd dirlilr;   xm =m palpha.mod -lilr=lilr -dbg=$(DBG)
	mv dirlilr/palpha ${MACHINE}

progsilr:
	${MAKE} pgsilr LILR=silr
pgsilr:
	cd dirsilr;   xm =m latsr.mod -lilr=silr -dbg=$(DBG)
	mv dirsilr/latsr ${MACHINE}
	cd dirsilr;   xm =m seeksr.mod -lilr=silr -dbg=$(DBG)
	mv dirsilr/seeksr ${MACHINE}

progsisi:
	${MAKE} pgsisi LILR=sisi
pgsisi:
	cd dirsisi;   xm =m seeks.mod -lilr=sisi -dbg=$(DBG)
	mv dirsisi/seeks ${MACHINE}
	cd dirsisi;   xm =m lats.mod -lilr=sisi -dbg=$(DBG)
	mv dirsisi/lats ${MACHINE}
	cd dirsisi;   xm =m menumrg.mod -lilr=sisi -dbg=$(DBG)
	mv dirsisi/menumrg ${MACHINE}
	cd dirsisi;   xm =m maxper.mod -lilr=sisi -dbg=$(DBG)
	mv dirsisi/maxper ${MACHINE}
	cd dirsisi;   xm =m streams.mod -lilr=sisi -dbg=$(DBG)
	mv dirsisi/streams ${MACHINE}
	cd dirsisi;   xm =m maketab.mod -lilr=sisi -dbg=$(DBG)
	mv dirsisi/maketab ${MACHINE}

${PROGLILR}: % : dirlilr/%.mod
	xm =m $< -lilr=lilr $(LOOK1) ${BIBLIO}

${PROGSILR}: % : dirsilr/%.mod
	xm =m $< -lilr=silr $(LOOK1) ${BIBLIO}

${PROGSISI}: % : dirsisi/%.mod
	xm =m $< -lilr=sisi $(LOOK1) ${BIBLIO} 

cleanall:  clean cleanprog
	-rm -f *.o *.dvi *.bbl *.blg *.toc
	-rm ${DEF1} ${DEF3} ${DEF4} *.sym

cleanprog:
	-cd $(MACHINE); rm ${PROGLILR};  rm ${PROGSILR}; rm ${PROGSISI};\
            rm select

clean:
	-rm -f *~ *.bck *% *.bak *.aux *.log core




#======================== BIBLIOTHEQUES ============================

LIB = $(XDSLIB)/liblat${LILR}.a

lib: cpsym cph
	@ echo "==================================================="
	@ echo "Construction de la bibliotheque ${LIB}"
	@ ar r ${LIB} ${OBJ2} ${OBJ3}
	@ echo
	@ echo "Contenu de la bibliotheque ${LIB}"
	@ echo
	@ ar t ${LIB}
	@ echo ""
	@ echo "==================================================="

cpsym:
	cp ${SYM2} ${XDSSYM}/dir${LILR}
	cp ${SYM3} ${XDSSYM}/dir${LILR}

cph :
	cp ${HHH2} ${XDSINC}/dir${LILR}
	cp ${HHH3} ${XDSINC}/dir${LILR}

dellib:
	-rm ${XDSLIB}/liblatlilr.a \
            ${XDSLIB}/liblatsilr.a \
            ${XDSLIB}/liblatsisi.a 
