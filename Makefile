# Unix makefile for tigermain example

HOME=~
MOSMLHOME=/usr/
MOSMLTOOLS=camlrunm /usr/share/mosml/tools
MOSMLLEX=mosmllex
MOSMLYACC=mosmlyac -v

GCC=gcc
CFLAGS= -g
MOSMLC=/usr/bin/mosmlc -c -liberal
MOSMLL=/usr/bin/mosmlc

# Unix
REMOVE=rm -f
MOVE=mv
EXEFILE=

# DOS
#REMOVE=del
#MOVE=move
#EXEFILE=.exe

.SUFFIXES :
.SUFFIXES : .sig .sml .ui .uo

GRALOBJS= tigerabs.uo tigergrm.uo tigerlex.uo tigermain.uo \
	tigernlin.uo tigerpp.uo tigerescap.uo tigertab.uo \
	tigerseman.uo tigertemp.uo topsort.uo tigertopsort.uo \
	tigertrans.uo tigermuestratipos.ui tigermuestratipos.uo

all: tiger

tiger: $(GRALOBJS) $(OBJSGEN)
	$(MOSMLL) -o tiger $(EXEFILE) tigermain.uo

tigergrm.sml tigergrm.sig: tigergrm.y 
	$(MOSMLYACC) tigergrm.y

tigerlex.sml: tigerlex.lex
	$(MOSMLLEX) tigerlex.lex

clean:
	$(REMOVE) Makefile.bak
	$(REMOVE) tigergrm.output
	$(REMOVE) tigergrm.sig
	$(REMOVE) tigergrm.sml
	$(REMOVE) tigerlex.sml
	$(REMOVE) tigermain
	$(REMOVE) *.ui
	$(REMOVE) *.uo
	$(REMOVE) errlist
	$(REMOVE) *.o

.sig.ui:
	$(MOSMLC) $<

.sml.uo:
	$(MOSMLC) $<

depend: tigerabs.sml tigergrm.sml tigerlex.sml tigermain.sml \
	tigernlin.sml tigerpp.sml
	$(REMOVE) Makefile.bak
	$(MOVE) Makefile Makefile.bak
	$(MOSMLTOOLS)/cutdeps < Makefile.bak > Makefile
	$(MOSMLTOOLS)/mosmldep >> Makefile

### DO NOT DELETE THIS LINE
tigertab.uo: tigertab.ui 
tigerseman.ui: tigerabs.uo 
tigermain.uo: tigerseman.ui tigerescap.ui tigergrm.ui tigerlex.uo \
    tigerpp.uo 
tigermuestratipos.ui: tigertips.uo 
tigerescap.ui: tigerabs.uo 
tigermuestratipos.uo: tigermuestratipos.ui tigertips.uo 
tigersres.uo: tigertab.ui tigertips.uo tigertemp.ui tigerabs.uo 
tigerlex.uo: tigergrm.ui tigernlin.uo 
tigertopsort.uo: tigertopsort.ui tigertab.ui tigertips.uo tigerabs.uo \
    tigermuestratipos.ui 
tigertemp.uo: tigertemp.ui 
tigerpp.uo: tigerabs.uo 
tigergrm.ui: tigerabs.uo 
tigergrm.uo: tigergrm.ui tigernlin.uo tigerabs.uo 
tigerescap.uo: tigerescap.ui tigertab.ui tigerabs.uo 
tigertrans.uo: tigertrans.ui 
tigerseman.uo: tigerseman.ui tigersres.uo tigertab.ui tigertopsort.ui \
    tigertemp.ui tigerabs.uo tigertrans.ui 
tigertopsort.ui: tigertab.ui tigertips.uo tigerabs.uo 
