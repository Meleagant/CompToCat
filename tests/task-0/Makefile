.PHONY: all clean

JOUJOU=../../joujou --typecheck-eta --print-infer

GOODS = $(wildcard *-good.j0)
BADS  = $(wildcard *-bad.j0)

all:
	@ echo '* Task 0: Writing a typeinference' | tee task-0.log
	@for good in $(GOODS); do \
	  ($(JOUJOU) $$good && echo "  - [OK] $$good") || echo "  - [KO] $$good"; \
	done | tee -a task-0.log
	@for bad in $(BADS); do \
	  ($(JOUJOU) $$bad 2> $$bad.log && echo "  - [KO] $$bad") \
          || echo "  - [XFAIL] $$bad"; \
	  cat $$bad.log; \
	done | tee -a task-0.log
	@ echo '** Score for this task:' \
        `grep '\[OK\]\|\[XFAIL\]' task-0.log | wc -l`/\
	`grep '^  -' task-0.log | wc -l | tr -d ' '`

clean:
	rm -f *~ *.log
