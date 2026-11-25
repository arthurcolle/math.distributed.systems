"use strict";

const $ = (selector) => document.querySelector(selector);
const el = (tag, className, text) => {
  const node = document.createElement(tag);
  if (className) node.className = className;
  if (text !== undefined) node.textContent = text;
  return node;
};
const append = (parent, ...children) => children.forEach((child) => parent.append(child));
const state = {areas: [], lemmas: [], sources: [], tasks: [], summary: null, areaLimit: 40, sourceLimit: 30};

function links(text, href, className = "") {
  const node = el("a", className, text);
  node.href = href;
  return node;
}

function renderTasks() {
  const query = $("#task-search").value.trim().toLocaleLowerCase();
  const matches = state.tasks.filter((task) =>
    [task.title, task.summary, task.track, task.status, ...(task.codes || [])]
      .join(" ").toLocaleLowerCase().includes(query));
  const container = $("#task-list");
  container.replaceChildren();
  $("#task-count").textContent = `${matches.length} / ${state.tasks.length}`;
  if (!matches.length) { container.append(el("p", "empty", "No matching open tasks.")); return; }
  for (const task of matches) {
    const card = el("article", "task-card");
    const top = el("div", "task-top");
    append(top, el("span", "card-id", `TASK / ${task.number ? `#${task.number}` : task.id}`),
      el("span", `task-status ${task.status === "claimed" ? "claimed" : ""}`, task.status));
    const tags = el("div", "task-tags");
    tags.append(el("span", "tag", task.track));
    for (const code of task.codes || []) tags.append(el("span", "tag", code));
    const footer = el("div", "task-footer");
    footer.append(el("span", "task-owner", task.owner ? `Claimed by @${task.owner}` : "Open to contributors"));
    footer.append(links(task.owner ? "Discuss or review ↗" : "Claim this task ↗", task.url, "task-link"));
    append(card, top, el("h4", "", task.title), el("p", "", task.summary), tags, footer);
    container.append(card);
  }
}

function issueTask(issue) {
  const labels = issue.labels.map((label) => typeof label === "string" ? label : label.name);
  const section = (name) => {
    const match = issue.body?.match(new RegExp(`(?:^|\\n)## ${name}\\n([\\s\\S]*?)(?=\\n## |$)`, "i"));
    return match ? match[1].trim().replace(/\s+/g, " ") : "Open the issue for the exact proof obligation.";
  };
  const codes = labels.filter((label) => /^msc:[0-9]{2}[A-Z][0-9]{2}$/.test(label)).map((label) => label.slice(4));
  return {
    id: String(issue.number), number: issue.number, title: issue.title,
    summary: section("Proof obligation"),
    track: labels.find((label) => label.startsWith("track:"))?.slice(6) || "research",
    status: labels.includes("status:review") ? "review" : issue.assignees?.length ? "claimed" : "open",
    owner: issue.assignees?.[0]?.login || "", codes, url: issue.html_url,
  };
}

async function loadTasks(snapshot) {
  state.tasks = snapshot;
  $("#task-feed-state").textContent = "Committed task snapshot";
  renderTasks();
  const controller = new AbortController();
  const timer = setTimeout(() => controller.abort(), 6500);
  try {
    const response = await fetch("https://api.github.com/repos/arthurcolle/math.distributed.systems/issues?state=open&labels=research-task&per_page=100", {
      headers: {Accept: "application/vnd.github+json"}, signal: controller.signal, cache: "no-store",
    });
    if (!response.ok) throw new Error(`GitHub API ${response.status}`);
    const issues = await response.json();
    if (!Array.isArray(issues)) throw new Error("Invalid GitHub response");
    state.tasks = issues.filter((issue) => !issue.pull_request).map(issueTask);
    $("#task-feed-state").textContent = `Live from GitHub · ${state.tasks.length} open`;
    renderTasks();
  } catch (_) {
    $("#task-feed-state").textContent = "Committed task snapshot · live feed unavailable";
  } finally { clearTimeout(timer); }
}

function renderLemmas() {
  const query = $("#lemma-search").value.trim().toLocaleLowerCase();
  const matches = state.lemmas.filter((item) =>
    [item.title, item.kind, item.status, item.statement, item.use, ...item.codes]
      .join(" ").toLocaleLowerCase().includes(query));
  const container = $("#lemma-list");
  container.replaceChildren();
  $("#lemma-count").textContent = `${matches.length} / ${state.lemmas.length}`;
  if (!matches.length) {container.append(el("p", "empty", "No matching lemma cards.")); return;}
  for (const [index, item] of matches.entries()) {
    const card = el("article", "lemma-card");
    const top = el("div", "card-top");
    const statusClass = /Unproved/.test(item.status) ? "open" : /pending|Paper proof/.test(item.status) ? "pending" : "";
    append(top, el("span", "card-id", `LEMMA / ${String(index + 1).padStart(2,"0")}`), el("span", `status ${statusClass}`, item.status));
    const h = el("h3", "", item.title);
    const kind = el("div", "kind", item.kind);
    const statement = el("p", "statement", item.statement);
    const tags = el("div", "code-row");
    item.areas.forEach((area) => { const tag = links(area.code, `#atlas`, "tag"); tag.title = area.title; tags.append(tag); });
    const details = el("details", "card-details");
    details.append(el("summary", "", "Proof, stress test & provenance"));
    const body = el("div", "proof-block");
    for (const [label, value] of [["DERIVATION",item.proof],["ADVERSARIAL TEST",item.stress],["USE",item.use],["NOVELTY",item.novelty]]) {
      append(body, el("span", "proof-label", label), el("p", "", value));
    }
    body.append(links("Open artifact ↗", item.artifact, "artifact-link"));
    details.append(body);
    append(card, top, h, kind, statement, tags, details);
    container.append(card);
  }
}

function renderPair() {
  const a = Number($("#pair-a").value), b = Number($("#pair-b").value);
  const result = $("#pair-result");
  result.replaceChildren();
  if (!Number.isInteger(a) || !Number.isInteger(b) || a < 1 || b < 1 || a > 1000 || b > 1000 || a === b) {
    result.append(el("span", "muted", "Enter two different integer IDs from 1 to 1000."));
    return;
  }
  const i = Math.min(a,b), j = Math.max(a,b);
  const row = (i-1)*1000 - i*(i-1)/2 + (j-i);
  const left = state.areas[i-1], right = state.areas[j-1];
  append(result, el("strong", "", `Pair ${row.toLocaleString()}`),
    el("span", "muted", `  /  ${left.code} ${left.title}  ×  ${right.code} ${right.title}`));
}

function renderAreas(reset = false) {
  if (reset) state.areaLimit = 40;
  const query = $("#area-search").value.trim().toLocaleLowerCase();
  const matches = state.areas.filter((item) =>
    [item.id, item.code, item.top_class, item.title].join(" ").toLocaleLowerCase().includes(query));
  const body = $("#area-list");
  body.replaceChildren();
  for (const area of matches.slice(0, state.areaLimit)) {
    const row = el("tr");
    append(row, el("td", "", String(area.id)), el("td", "", area.code),
      el("td", "", area.title), el("td", "", area.lemmaCount ? String(area.lemmaCount) : "—"));
    body.append(row);
  }
  $("#area-count").textContent = `${matches.length} match${matches.length === 1 ? "" : "es"}`;
  $("#area-more").hidden = matches.length <= state.areaLimit;
}

function renderSources(reset = false) {
  if (reset) state.sourceLimit = 30;
  const query = $("#source-search").value.trim().toLocaleLowerCase();
  const matches = state.sources.filter((item) =>
    [item.id,item.title,item.abstractClaim,item.catalog].join(" ").toLocaleLowerCase().includes(query));
  const container = $("#source-list");
  container.replaceChildren();
  for (const item of matches.slice(0,state.sourceLimit)) {
    const row = el("div", "source-item");
    append(row, el("span", "source-label", item.id.replace("openai-","OA / ").replace("anthropic-","AN / ")),
      links(item.title, item.path), el("small", "", item.status));
    container.append(row);
  }
  if (!matches.length) container.append(el("p", "empty", "No matching source entries."));
  $("#source-count").textContent = `${matches.length} match${matches.length === 1 ? "" : "es"}`;
  $("#source-more").hidden = matches.length <= state.sourceLimit;
}

async function init() {
  try {
    const [areas, lemmas, sources, summary, tasks] = await Promise.all(
      ["data/areas.json","data/lemmas.index.json","data/sources.json","data/summary.json","data/tasks.json"]
        .map(async (path) => {const response = await fetch(path); if (!response.ok) throw new Error(`${path}: ${response.status}`); return response.json();}));
    Object.assign(state,{areas,lemmas,sources,summary});
    $("#hero-pairs").textContent = summary.pairs.toLocaleString();
    $("#hero-areas").textContent = summary.areas.toLocaleString();
    $("#hero-sources").textContent = summary.sources.toLocaleString();
    $("#hero-lemmas").textContent = summary.lemmas.toLocaleString();
    $("#class-coverage").textContent = `${Object.keys(summary.classCoverage).length} / ${summary.classes}`;
    $("#lemma-search").addEventListener("input",renderLemmas);
    $("#task-search").addEventListener("input",renderTasks);
    $("#area-search").addEventListener("input",()=>renderAreas(true));
    $("#source-search").addEventListener("input",()=>renderSources(true));
    $("#pair-go").addEventListener("click",renderPair);
    ["#pair-a","#pair-b"].forEach((selector)=>$(selector).addEventListener("keydown",(e)=>{if(e.key === "Enter") renderPair();}));
    $("#area-more").addEventListener("click",()=>{state.areaLimit+=40;renderAreas();});
    $("#source-more").addEventListener("click",()=>{state.sourceLimit+=30;renderSources();});
    renderLemmas();renderPair();renderAreas();renderSources();loadTasks(tasks);
  } catch (error) {
    $("#lemma-list").append(el("p","empty",`Could not load the research index: ${error.message}. Run python3 -m http.server from the repository root.`));
  }
}

init();
