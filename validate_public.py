#!/usr/bin/env python3
"""Read-only structural validation for the public atlas and swarm snapshot."""

import csv
import json
import re
from collections import Counter
from html.parser import HTMLParser
from pathlib import Path
from urllib.parse import urlparse

HERE = Path(__file__).resolve().parent
DATA = HERE / "data"
REPO = "https://github.com/arthurcolle/math.distributed.systems"


def load(name):
    return json.loads((DATA / name).read_text(encoding="utf-8"))


def internal_file(path):
    assert isinstance(path, str) and path and not path.startswith("/"), path
    resolved = (HERE / path).resolve()
    assert resolved.is_relative_to(HERE) and resolved.is_file(), path


class References(HTMLParser):
    def __init__(self):
        super().__init__()
        self.paths = []

    def handle_starttag(self, tag, attrs):
        attrs = dict(attrs)
        for key in ("href", "src"):
            value = attrs.get(key)
            if value and not value.startswith(("#", "https://", "mailto:")):
                self.paths.append(value.split("#", 1)[0])


def main():
    with (DATA / "areas1000.csv").open(newline="", encoding="utf-8") as stream:
        csv_areas = list(csv.DictReader(stream))
    areas = load("areas.json")
    assert len(csv_areas) == len(areas) == 1000
    assert [int(item["id"]) for item in csv_areas] == list(range(1, 1001))
    codes = {item["code"] for item in csv_areas}
    assert len(codes) == 1000
    for raw, area in zip(csv_areas, areas):
        assert all(area[key] == raw[key] for key in ("code", "top_class", "subclass", "title"))
        assert area["id"] == int(raw["id"])

    lemmas = load("lemmas.json")
    indexed = load("lemmas.index.json")
    assert len({item["id"] for item in lemmas}) == len(lemmas)
    assert len(lemmas) == len(indexed)
    covered = Counter()
    for raw, item in zip(lemmas, indexed):
        assert all(key in raw for key in ("id", "title", "status", "statement", "proof", "stress", "novelty", "use", "artifact", "source", "codes"))
        assert raw["codes"] and len(set(raw["codes"])) == len(raw["codes"])
        assert all(code in codes for code in raw["codes"]), raw["id"]
        internal_file(raw["artifact"])
        assert {**raw, "areas": item["areas"]} == item, raw["id"]
        assert item["areas"] == [
            {"id": int(next(area["id"] for area in csv_areas if area["code"] == code)),
             "code": code, "title": next(area["title"] for area in csv_areas if area["code"] == code)}
            for code in raw["codes"]
        ], raw["id"]
        covered.update(raw["codes"])
    assert all(area["lemmaCount"] == covered[area["code"]] for area in areas)

    sources = load("sources.json")
    assert len({item["id"] for item in sources}) == len(sources)
    for source in sources:
        assert all(key in source for key in ("id", "title", "catalog", "status", "path"))
        assert urlparse(source["path"]).scheme == "https"
        assert urlparse(source["path"]).hostname == "github.com"

    tasks = load("tasks.json")
    assert len({item["id"] for item in tasks}) == len(tasks)
    numbers = [item["number"] for item in tasks if item["number"] is not None]
    assert len(set(numbers)) == len(numbers)
    for task in tasks:
        assert re.fullmatch(r"[a-z0-9-]+", task["id"])
        assert all(key in task for key in ("title", "summary", "track", "status", "codes", "adversarial_test", "deliverable", "source_card", "url"))
        assert task["status"] in {"open", "claimed", "review"}
        assert task["codes"] and all(code in codes for code in task["codes"])
        assert task["source_card"] == "" or task["source_card"] in {item["id"] for item in lemmas}
        assert task["url"].startswith(REPO + "/issues/")
        if task["number"] is not None:
            assert type(task["number"]) is int and task["number"] > 0
            assert task["url"] == f"{REPO}/issues/{task['number']}"

    summary = load("summary.json")
    assert (summary["areas"], summary["pairs"], summary["lemmas"], summary["sources"]) == (1000, 499500, len(lemmas), len(sources))
    assert summary["coveredAreas"] == len(covered)
    assert summary["unreviewedAreas"] == 1000 - len(covered)
    parser = References()
    parser.feed((HERE / "index.html").read_text(encoding="utf-8"))
    for path in parser.paths:
        internal_file(path)
    print(f"PASS: 1,000 areas, 499,500 pairs, {len(lemmas)} cards, {len(sources)} sources, {len(tasks)} tasks; {len(parser.paths)} local page references")


if __name__ == "__main__":
    main()
