SUBDIRS = verif/btrees/. \
					verif/trie/.

all: $(SUBDIRS)
$(SUBDIRS):
	$(MAKE) -C $@

clean:
	rm -rf verif/**/*.vo verif/**/*.glob verif/**/.*.aux

.PHONY: all $(SUBDIRS)
