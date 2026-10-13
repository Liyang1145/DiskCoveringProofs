PYTHON ?= python

.PHONY: verify restore
verify:
	$(PYTHON) tools/verify_delivery.py

restore:
	$(PYTHON) tools/restore_large_files.py --destination ../restored
