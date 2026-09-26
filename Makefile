.PHONY: challenges-challenge-only challenges-trusted

# Comparator-safe target: never elaborates a standalone Solution.lean file.
challenges-challenge-only:
	./scripts/build-challenges.sh --challenge-only

# Intended only for a reviewed repository checkout.
challenges-trusted:
	./scripts/build-challenges.sh --trusted-all
