(() => {
  "use strict";

  const REGISTRY_URL = "data/artifacts/registry.jsonld";
  const FORMAL_TYPES = new Set([
    "FormalTheorem", "FormalLemma", "FormalDefinition", "FormalAxiom", "FormalStructure", "FormalModule",
  ]);

  function text(parent, tag, value, className) {
    const element = document.createElement(tag);
    if (className) element.className = className;
    element.textContent = value;
    parent.append(element);
    return element;
  }

  function link(parent, label, href) {
    const element = document.createElement("a");
    element.href = href;
    element.target = "_blank";
    element.rel = "noopener noreferrer";
    element.textContent = label;
    parent.append(element);
    return element;
  }

  function paperUrl(paper) {
    return paper.referenceUrl || (paper.arxivId ? `https://arxiv.org/abs/${paper.arxivId}` : null);
  }

  function populateMetrics(registry) {
    const graph = registry["@graph"] || [];
    const metrics = {
      artifacts: graph.length,
      formal: graph.filter((artifact) => FORMAL_TYPES.has(artifact["@type"])).length,
      open: graph.filter((artifact) => artifact.openProblem).length,
      sources: graph.filter((artifact) => artifact["@type"] === "SourcePaper" && artifact.citation).length,
    };
    document.querySelectorAll("[data-registry-metric]").forEach((element) => {
      const metric = element.dataset.registryMetric;
      if (Object.hasOwn(metrics, metric)) element.textContent = String(metrics[metric]);
    });
  }

  function populateReferences(registry) {
    const byId = new Map((registry["@graph"] || []).map((artifact) => [artifact["@id"], artifact]));
    const authors = new Map();
    for (const edge of registry.relationships || []) {
      if (edge.predicate !== "authoredBy") continue;
      const names = authors.get(edge.source) || [];
      const author = byId.get(edge.target);
      if (author?.name) names.push(author.name);
      authors.set(edge.source, names);
    }
    document.querySelectorAll("[data-reference-ids]").forEach((container) => {
      const ids = container.dataset.referenceIds.split(",").map((id) => id.trim()).filter(Boolean);
      const items = ids.map((id) => byId.get(id)).filter(Boolean);
      if (!items.length) return;
      const list = document.createElement("ol");
      list.className = "reference-ledger-list";
      for (const paper of items) {
        const item = document.createElement("li");
        item.className = "reference-ledger-item";
        const url = paperUrl(paper);
        if (url) link(item, paper.name, url);
        else text(item, "strong", paper.name);
        const names = authors.get(paper["@id"]) || [];
        if (names.length) text(item, "span", names.join(", "), "reference-authors");
        text(item, "p", paper.citation || [paper.name, paper.year].filter(Boolean).join(" (") + (paper.year ? ")" : ""));
        list.append(item);
      }
      container.replaceChildren(list);
    });
  }

  async function start() {
    try {
      const response = await fetch(REGISTRY_URL, { cache: "no-cache" });
      if (!response.ok) throw new Error(`registry returned ${response.status}`);
      const registry = await response.json();
      if (!Array.isArray(registry["@graph"]) || !Array.isArray(registry.relationships)) throw new Error("invalid registry");
      populateMetrics(registry);
      populateReferences(registry);
    } catch (error) {
      console.warn("Reference ledger unavailable", error);
    }
  }

  start();
})();
