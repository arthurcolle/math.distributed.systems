#!/usr/bin/env python3
"""Rebuild the standalone public atlas from committed source data."""

import csv
import json
from collections import Counter
from pathlib import Path

HERE = Path(__file__).resolve().parent
DATA = HERE / "data"


def read_json(name):
    return json.loads((DATA / name).read_text(encoding="utf-8"))


def dump(name, value):
    (DATA / name).write_text(
        json.dumps(value, ensure_ascii=False, separators=(",", ":")) + "\n",
        encoding="utf-8",
    )


def main():
    with (DATA / "areas1000.csv").open(newline="", encoding="utf-8") as stream:
        areas = list(csv.DictReader(stream))
    assert len(areas) == 1000
    assert [int(area["id"]) for area in areas] == list(range(1, 1001))
    area_by_code = {area["code"]: area for area in areas}
    assert len(area_by_code) == 1000

    lemmas = read_json("lemmas.json")
    assert len({item["id"] for item in lemmas}) == len(lemmas)
    required = {"id", "title", "kind", "status", "novelty", "codes",
                "statement", "proof", "stress", "use", "artifact", "source"}
    for lemma in lemmas:
        assert required <= lemma.keys(), lemma.get("id")
        assert lemma["codes"] and len(set(lemma["codes"])) == len(lemma["codes"])
        assert all(code in area_by_code for code in lemma["codes"]), lemma["id"]
        artifact = (HERE / lemma["artifact"]).resolve()
        assert artifact.is_relative_to(HERE) and artifact.is_file(), lemma["id"]
        lemma["areas"] = [
            {"id": int(area_by_code[code]["id"]), "code": code,
             "title": area_by_code[code]["title"]}
            for code in lemma["codes"]
        ]

    sources = read_json("sources.json")
    assert len({item["id"] for item in sources}) == len(sources)
    assert all(item["path"].startswith("https://github.com/") for item in sources)

    tasks = read_json("tasks.json")
    assert len({item["id"] for item in tasks}) == len(tasks)
    lemma_ids = {item["id"] for item in lemmas}
    for task in tasks:
        assert task["codes"] and all(code in area_by_code for code in task["codes"]), task["id"]
        assert task["status"] in {"open", "claimed", "review"}, task["id"]
        assert task["source_card"] == "" or task["source_card"] in lemma_ids
        assert task["url"].startswith("https://github.com/arthurcolle/math.distributed.systems/issues/")

    covered = Counter(code for lemma in lemmas for code in lemma["codes"])
    for area in areas:
        area["id"] = int(area["id"])
        area["lemmaCount"] = covered[area["code"]]
    class_counts = Counter(area["top_class"] for area in areas)
    class_coverage = Counter(area["top_class"] for area in areas if area["lemmaCount"])

    dump("areas.json", areas)
    dump("lemmas.index.json", lemmas)
    dump("summary.json", {
        "areas": len(areas), "pairs": len(areas) * (len(areas)-1) // 2,
        "classes": len(class_counts), "sources": len(sources),
        "lemmas": len(lemmas), "coveredAreas": len(covered),
        "unreviewedAreas": len(areas) - len(covered),
        "classCounts": class_counts, "classCoverage": class_coverage,
        "atlasSource": "data/manifest1000.json",
        "catalogSource": "data/sources.json",
    })
    with (DATA / "area-audit-queue.csv").open("w", newline="", encoding="utf-8") as stream:
        writer = csv.writer(stream)
        writer.writerow(["id", "code", "title", "lemma_cards", "review_state"])
        for area in areas:
            writer.writerow([area["id"], area["code"], area["title"], area["lemmaCount"],
                             "lemma card exists; literature audit pending" if area["lemmaCount"] else "unreviewed"])
    with (DATA / "class-audit-queue.csv").open(newline="", encoding="utf-8") as stream:
        class_titles = {row["msc_class"]: row["title"] for row in csv.DictReader(stream)}
    assert set(class_titles) == set(class_counts)
    with (DATA / "class-audit-queue.csv").open("w", newline="", encoding="utf-8") as stream:
        writer = csv.writer(stream)
        writer.writerow(["msc_class", "title", "selected_areas", "areas_with_cards", "review_state"])
        for code in sorted(class_counts):
            writer.writerow([code, class_titles[code], class_counts[code], class_coverage[code],
                             "partial" if class_coverage[code] else "unreviewed"])
    print(f"Indexed {len(areas)} areas, {len(sources)} corpus sources, "
          f"{len(lemmas)} lemma cards and {len(tasks)} swarm tasks.")


if __name__ == "__main__":
    main()
