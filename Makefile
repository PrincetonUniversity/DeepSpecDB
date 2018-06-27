SUBDIRS = verif/btrees/. \
					verif/trie/. \
          memmgr/.

all: $(SUBDIRS)
$(SUBDIRS):
	$(MAKE) -C $@

clean:
	rm -rf memmgr/*.vo memmgr/*.glob memmgr/.*.aux \
         verif/**/*.vo verif/**/*.glob verif/**/.*.aux

.PHONY: all $(SUBDIRS)
