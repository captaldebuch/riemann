(() => {
  "use strict";

  const REGISTRY_URL = "data/artifacts/registry.jsonld";
  const PAGE_SIZE = 24;
  const FORMAL_TYPES = new Set([
    "FormalTheorem",
    "FormalLemma",
    "FormalDefinition",
    "FormalAxiom",
    "FormalStructure",
    "FormalModule",
  ]);

  const state = {
    artifacts: [],
    byId: new Map(),
    outgoing: new Map(),
    incoming: new Map(),
    selectedId: null,
    visible: PAGE_SIZE,
    auditFilter: "",
  };

  const elements = {
    artifactCount: document.querySelector("#artifact-count"),
    relationshipCount: document.querySelector("#relationship-count"),
    formalCount: document.querySelector("#formal-count"),
    openCount: document.querySelector("#open-count"),
    search: document.querySelector("#artifact-search"),
    type: document.querySelector("#artifact-type"),
    status: document.querySelector("#artifact-status"),
    openOnly: document.querySelector("#artifact-open-only"),
    clear: document.querySelector("#artifact-clear"),
    summary: document.querySelector("#result-summary"),
    results: document.querySelector("#artifact-results"),
    more: document.querySelector("#artifact-more"),
    detail: document.querySelector("#artifact-detail"),
  };

  const humanize = (value) => value.replace(/([a-z])([A-Z])/g, "$1 $2").replace(/[-_]/g, " ");
  const titleCase = (value) => humanize(value).replace(/\b\w/g, (letter) => letter.toUpperCase());
  const safeText = (value) => String(value ?? "");

  function statusOf(artifact) {
    return artifact.verification?.status || "unknown";
  }

  function statusLabel(status) {
    return {
      proved: "Proved",
      assumed: "Assumed / research gate",
      "contains_sorry": "Contains sorry",
      declaration: "Declaration",
      unknown: "Unclassified",
    }[status] || titleCase(status);
  }

  function auditStatusLabel(status) {
    return {
      reviewed: "Audit reviewed",
      pending: "Audit pending",
      rejected: "Route rejected",
    }[status] || titleCase(status);
  }

  function paperClaimValidityLabel(status) {
    return {
      sound: "Paper claim sound in scope",
      conditional: "Paper claim conditional",
      scope_mismatch: "Paper claim scope mismatch",
      unsupported: "Paper claim unsupported",
      contradicted: "Paper claim contradicted",
      unreviewed: "Paper claim unreviewed",
    }[status] || titleCase(status);
  }

  function paperClaimStatus(artifact) {
    return artifact.paperClaims?.[0]?.validity?.status || "";
  }

  function appendText(parent, tagName, text, className) {
    const element = document.createElement(tagName);
    if (className) element.className = className;
    element.textContent = text;
    parent.append(element);
    return element;
  }

  function githubSourceUrl(source) {
    if (!source?.file) return null;
    const revision = source.commit || "main";
    const line = source.line ? `#L${source.line}` : "";
    return `https://github.com/captaldebuch/riemann/blob/${encodeURIComponent(revision)}/${source.file}${line}`;
  }

  function externalReferenceUrl(artifact) {
    return artifact.referenceUrl || (artifact.arxivId ? `https://arxiv.org/abs/${artifact.arxivId}` : null);
  }

  function addLink(parent, label, href, className) {
    const link = document.createElement("a");
    link.href = href;
    link.textContent = label;
    if (className) link.className = className;
    parent.append(link);
    return link;
  }

  function indexRegistry(registry) {
    state.artifacts = [...registry["@graph"]].sort((left, right) => left.name.localeCompare(right.name));
    state.byId = new Map(state.artifacts.map((artifact) => [artifact["@id"], artifact]));
    state.outgoing = new Map();
    state.incoming = new Map();
    for (const relationship of registry.relationships || []) {
      const outgoing = state.outgoing.get(relationship.source) || [];
      outgoing.push(relationship);
      state.outgoing.set(relationship.source, outgoing);
      const incoming = state.incoming.get(relationship.target) || [];
      incoming.push(relationship);
      state.incoming.set(relationship.target, incoming);
    }

    const kinds = [...new Set(state.artifacts.map((artifact) => artifact["@type"]))].sort();
    for (const kind of kinds) {
      const option = document.createElement("option");
      option.value = kind;
      option.textContent = titleCase(kind);
      elements.type.append(option);
    }

    const openCount = state.artifacts.filter((artifact) => artifact.openProblem).length;
    const formalCount = state.artifacts.filter((artifact) => FORMAL_TYPES.has(artifact["@type"])).length;
    elements.artifactCount.textContent = String(state.artifacts.length);
    elements.relationshipCount.textContent = String((registry.relationships || []).length);
    elements.formalCount.textContent = String(formalCount);
    elements.openCount.textContent = String(openCount);
  }

  function matchingArtifacts() {
    const query = elements.search.value.trim().toLowerCase();
    const type = elements.type.value;
    const status = elements.status.value;
    const openOnly = elements.openOnly.checked;
    return state.artifacts.filter((artifact) => {
      if (type && artifact["@type"] !== type) return false;
      if (status && statusOf(artifact) !== status) return false;
      if (openOnly && !artifact.openProblem) return false;
      if (state.auditFilter === "h15" && !artifact.rolesInH15?.length) return false;
      if (!query) return true;
      const haystack = [
        artifact.name,
        artifact.statement,
        artifact.summary,
        artifact.abstract,
        artifact.auditStatus,
        artifact.findings,
        ...(artifact.paperClaims || []).flatMap((paperClaim) => [
          paperClaim.claim,
          paperClaim.sourcePaper,
          paperClaim.validity?.status,
          paperClaim.validity?.note,
          ...(paperClaim.validity?.conditions || []),
        ]),
        ...(artifact.authors || []),
        ...(artifact.rolesInH15 || []),
        artifact["@id"],
        ...(artifact.tags || []),
      ].join(" ").toLowerCase();
      return haystack.includes(query);
    });
  }

  function renderResults() {
    const matches = matchingArtifacts();
    const displayed = matches.slice(0, state.visible);
    elements.results.replaceChildren();
    elements.summary.textContent = `${matches.length} matching artifact${matches.length === 1 ? "" : "s"}`;
    if (!displayed.length) {
      appendText(elements.results, "li", "No artifacts match these filters.", "artifact-empty");
      elements.more.hidden = true;
      return;
    }
    for (const artifact of displayed) {
      const item = document.createElement("li");
      const button = document.createElement("button");
      button.className = "artifact-result-button";
      button.type = "button";
      button.setAttribute("aria-pressed", String(state.selectedId === artifact["@id"]));
      button.addEventListener("click", () => selectArtifact(artifact["@id"]));
      appendText(button, "span", artifact.name, "artifact-result-name");
      const claimStatus = paperClaimStatus(artifact);
      const metadata = claimStatus
        ? `${titleCase(artifact["@type"])} · ${paperClaimValidityLabel(claimStatus)}`
        : artifact.auditStatus
        ? `${titleCase(artifact["@type"])} · ${auditStatusLabel(artifact.auditStatus)}`
        : `${titleCase(artifact["@type"])} · ${statusLabel(statusOf(artifact))}`;
      appendText(button, "span", metadata, "artifact-result-meta");
      item.append(button);
      elements.results.append(item);
    }
    elements.more.hidden = displayed.length >= matches.length;
    elements.more.textContent = `Show ${Math.min(PAGE_SIZE, matches.length - displayed.length)} more`;
  }

  function detailRelationship(item, relationship) {
    const target = state.byId.get(relationship.target);
    const row = document.createElement("li");
    appendText(row, "span", titleCase(relationship.predicate), "artifact-relationship-predicate");
    if (target) {
      const button = document.createElement("button");
      button.type = "button";
      button.className = "artifact-relation-button";
      button.textContent = target.name;
      button.addEventListener("click", () => selectArtifact(target["@id"]));
      row.append(button);
    } else {
      appendText(row, "code", relationship.target);
    }
    if (relationship.note) appendText(row, "span", ` — ${relationship.note}`);
    item.append(row);
  }

  function relationshipSection(title, relationships) {
    if (!relationships?.length) return null;
    const section = document.createElement("section");
    appendText(section, "h4", title);
    const list = document.createElement("ul");
    for (const relationship of relationships) detailRelationship(list, relationship);
    section.append(list);
    return section;
  }

  function selectArtifact(id) {
    const artifact = state.byId.get(id);
    if (!artifact) return;
    state.selectedId = id;
    elements.detail.replaceChildren();
    const heading = document.createElement("h3");
    heading.textContent = artifact.name;
    elements.detail.append(heading);
    appendText(elements.detail, "p", artifact["@id"], "artifact-id");

    const metadata = document.createElement("div");
    appendText(metadata, "span", titleCase(artifact["@type"]), "artifact-type");
    appendText(metadata, "span", statusLabel(statusOf(artifact)), `artifact-status artifact-status-${statusOf(artifact)}`);
    if (artifact.openProblem) appendText(metadata, "span", "Open research gate", "artifact-status artifact-status-assumed");
    const claimStatus = paperClaimStatus(artifact);
    if (claimStatus) appendText(metadata, "span", paperClaimValidityLabel(claimStatus), `artifact-status artifact-claim-status-${claimStatus}`);
    elements.detail.append(metadata);

    if (artifact.summary) {
      const section = document.createElement("section");
      appendText(section, "h4", "Recorded summary");
      appendText(section, "p", artifact.summary);
      elements.detail.append(section);
    }
    if (artifact.statement) {
      const section = document.createElement("section");
      appendText(section, "h4", "Formal statement header");
      const code = document.createElement("code");
      code.textContent = artifact.statement;
      section.append(code);
      elements.detail.append(section);
    }
    if (artifact.source?.file) {
      const section = document.createElement("section");
      appendText(section, "h4", "Recorded source");
      const location = document.createElement("p");
      const link = githubSourceUrl(artifact.source);
      if (link) addLink(location, `${artifact.source.file}:${artifact.source.line || 1}`, link);
      else appendText(location, "code", `${artifact.source.file}:${artifact.source.line || 1}`);
      if (artifact.source.module) appendText(location, "span", ` · ${artifact.source.module}`);
      section.append(location);
      elements.detail.append(section);
    }
    if (artifact.citation || externalReferenceUrl(artifact)) {
      const section = document.createElement("section");
      appendText(section, "h4", "Bibliographic reference");
      if (artifact.citation) appendText(section, "p", artifact.citation);
      const referenceUrl = externalReferenceUrl(artifact);
      if (referenceUrl) {
        const paragraph = document.createElement("p");
        addLink(paragraph, "Open cited source", referenceUrl);
        section.append(paragraph);
      }
      elements.detail.append(section);
    }
    if (artifact.authors?.length) {
      const section = document.createElement("section");
      appendText(section, "h4", "Authors");
      appendText(section, "p", artifact.authors.join(", "));
      elements.detail.append(section);
    }
    if (artifact.paperClaims?.length) {
      const section = document.createElement("section");
      appendText(section, "h4", "Paper-claim validity review");
      for (const paperClaim of artifact.paperClaims) {
        const review = document.createElement("article");
        review.className = "artifact-claim-review";
        const source = state.byId.get(paperClaim.sourcePaper);
        appendText(review, "p", source?.name || paperClaim.sourcePaper, "artifact-claim-source");
        const reviewStatus = paperClaim.validity?.status || "unreviewed";
        appendText(review, "span", paperClaimValidityLabel(reviewStatus), `artifact-status artifact-claim-status-${reviewStatus}`);
        if (paperClaim.sourceLocation) {
          const bits = [paperClaim.sourceLocation.theorem, paperClaim.sourceLocation.section, paperClaim.sourceLocation.equation]
            .filter(Boolean);
          if (paperClaim.sourceLocation.page) bits.push(`p. ${paperClaim.sourceLocation.page}`);
          if (bits.length) appendText(review, "p", `Source location: ${bits.join(", ")}`);
        }
        appendText(review, "p", `Claim: ${paperClaim.claim}`);
        if (paperClaim.validity?.conditions?.length) {
          appendText(review, "p", `Conditions: ${paperClaim.validity.conditions.join("; ")}`);
        }
        const methods = paperClaim.validity?.method?.join(", ");
        if (methods) appendText(review, "p", `Review: ${methods} · ${paperClaim.validity.reviewedAt || "date unrecorded"}`);
        if (paperClaim.validity?.note) appendText(review, "p", paperClaim.validity.note, "artifact-claim-note");
        section.append(review);
      }
      elements.detail.append(section);
    }
    if (artifact.auditStatus || artifact.rolesInH15?.length || artifact.findings) {
      const section = document.createElement("section");
      appendText(section, "h4", "H15 paper audit");
      if (artifact.auditStatus) appendText(section, "p", `Status: ${auditStatusLabel(artifact.auditStatus)}`);
      if (artifact.rolesInH15?.length) {
        const list = document.createElement("ul");
        for (const role of artifact.rolesInH15) appendText(list, "li", role);
        section.append(list);
      }
      if (artifact.findings) appendText(section, "p", artifact.findings);
      elements.detail.append(section);
    }
    if (artifact.localPdf) {
      const section = document.createElement("section");
      appendText(section, "h4", "Local archive record");
      if (artifact.publishedPdf) {
        const paragraph = document.createElement("p");
        addLink(paragraph, "Download archived PDF", artifact.publishedPdf);
        section.append(paragraph);
      }
      appendText(section, "code", artifact.localPdf);
      elements.detail.append(section);
    }
    if (artifact.tags?.length) {
      const section = document.createElement("section");
      appendText(section, "h4", "Tags");
      const tags = document.createElement("div");
      for (const tag of artifact.tags) appendText(tags, "span", tag, "artifact-tag");
      section.append(tags);
      elements.detail.append(section);
    }
    const outgoing = relationshipSection("Evidence and dependencies", state.outgoing.get(id));
    const incoming = relationshipSection("Referenced by", state.incoming.get(id));
    if (outgoing) elements.detail.append(outgoing);
    if (incoming) elements.detail.append(incoming);
    renderResults();
  }

  function resetFilters() {
    elements.search.value = "";
    elements.type.value = "";
    elements.status.value = "";
    elements.openOnly.checked = false;
    state.visible = PAGE_SIZE;
    state.auditFilter = "";
    renderResults();
  }

  function bindControls() {
    for (const control of [elements.search, elements.type, elements.status, elements.openOnly]) {
      control.addEventListener("input", () => {
        state.visible = PAGE_SIZE;
        renderResults();
      });
      control.addEventListener("change", () => {
        state.visible = PAGE_SIZE;
        renderResults();
      });
    }
    elements.clear.addEventListener("click", resetFilters);
    elements.more.addEventListener("click", () => {
      state.visible += PAGE_SIZE;
      renderResults();
    });
  }

  function applyQueryFilters() {
    const query = new URLSearchParams(window.location.search);
    const requestedType = query.get("type");
    const requestedStatus = query.get("status");
    const requestedSearch = query.get("query");
    if (requestedType && [...elements.type.options].some((option) => option.value === requestedType)) {
      elements.type.value = requestedType;
    }
    if (requestedStatus && [...elements.status.options].some((option) => option.value === requestedStatus)) {
      elements.status.value = requestedStatus;
    }
    if (requestedSearch) elements.search.value = requestedSearch;
    if (query.get("audit") === "h15") state.auditFilter = "h15";
    if (query.get("open") === "true") elements.openOnly.checked = true;
  }

  async function start() {
    try {
      const response = await fetch(REGISTRY_URL, { cache: "no-cache" });
      if (!response.ok) throw new Error(`registry request failed with ${response.status}`);
      const registry = await response.json();
      if (!Array.isArray(registry["@graph"]) || !Array.isArray(registry.relationships)) {
        throw new Error("registry payload has an unexpected shape");
      }
      indexRegistry(registry);
      bindControls();
      applyQueryFilters();
      renderResults();
      const firstResult = matchingArtifacts()[0] || state.artifacts.find((artifact) => artifact.openProblem);
      if (firstResult) selectArtifact(firstResult["@id"]);
    } catch (error) {
      elements.summary.textContent = "Registry unavailable";
      elements.detail.replaceChildren();
      appendText(elements.detail, "p", "The artifact registry could not be loaded. Download the JSON-LD file or retry after the site has finished publishing.", "artifact-detail-placeholder");
      console.error("Could not load artifact registry", error);
    }
  }

  start();
})();
