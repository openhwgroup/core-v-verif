all: doc

doc: RVVI.png
	eog $^
	
%.png: %.dot
	dot -Tpng $^ -o $@
	
clean:
	- rm -f RVVI.png