<p align="right">
  <a href="https://dendritic.oeiuwq.com/sponsor"><img src="https://img.shields.io/badge/sponsor-vic-white?logo=githubsponsors&logoColor=white&labelColor=%23FF0000" alt="Sponsor Vic"/></a>
  <a href="https://deepwiki.com/denful/dnx"><img src="https://deepwiki.com/badge.svg" alt="Ask DeepWiki"></a>
  <a href="https://github.com/denful/den/releases"><img src="https://img.shields.io/github/v/release/denful/dnx?style=plastic&logo=github&color=purple"/></a>
  <a href="https://dendritic.oeiuwq.com"><img src="https://img.shields.io/badge/Dendritic-Nix-informational?logo=nixos&logoColor=white" alt="Dendritic Nix"/></a>
  <a href="LICENSE"><img src="https://img.shields.io/github/license/denful/dnx" alt="License"/></a>
  <a href="https://github.com/denful/dnx/actions"><img src="https://github.com/denful/dnx/actions/workflows/test.yml/badge.svg" alt="CI Status"/></a>
</p>

> dnx and [vic](https://bsky.app/profile/oeiuwq.bsky.social)'s [nix libs](https://dendritic.oeiuwq.com) made for you with Love++. If you like my work, consider [sponsoring](#sustaining-dnx).

# δ-nx, one optimal engine for reproducible builds, multi language, verifiable and distributable computations.

**Why:** I got a fever dream about package managers, language runtimes, and proof assistants are secretly the *same* problem, the deterministic evaluation of content-addressed expressions, and a single, mathematically grounded engine can serve all three.

`dnx` is that engine. One rootless Rust binary on top of **Δ-Nets**: an interaction-net model that reduces programs **optimally** (never the same work twice), **in parallel by construction**, with **perfect confluence**. The same core that builds your packages runs more than one language, remembers work by its *meaning*, and machine-checks proofs about it.

> [design docs](https://github.com/denful/dnx/tree/design) · [slides from docs](https://notebooklm.google.com/notebook/6f8ed0c7-be75-4dd4-a531-82c7b137c9fd/artifact/6d0cc028-e56d-4efe-9686-5f7d4a0fc646)

---

## Why now

For decades these three worlds, building software, running languages, and proving them correct, have been built three separate times, on three separate stacks, each one redoing the others' work. The mathematics says they don't have to be. A year ago I found a paper about [Delta nets](https://github.com/danaugrs/deltanets), that give a single substrate that is confluent (one answer, always), optimal (no wasted step), and inherently parallel (it was *born* concurrent). `dnx` is my attempt to finally build computing on that substrate, out loud, in the open, as a public good. Since then I've spent that whole year trying to implement it correctly and performant as a new Nix engine, but dnx is not limited to Nix, nix is the first surface language to it, imagine using python-like or other existing syntax and have all of Nix power/packages for free.

That bet is becoming real: **general recursion, long the central open problem for this style of engine, now evaluates natively.** The list and higher-order-function layer that rests on it is unblocking behind it. This is early, fast-moving research software, and I am honest about its edges: the properties are proven on the model, the full vision is still being built, and that is exactly the work your support funds.

The goal is not only an alternative Nix. dnx is inspired by awesome software like Unison (distributable, content-hashed computations - not just derivations like Nix), and Lean4 for verifiable software (and system builds and derivations).

---

## What it makes possible

- **Never compute the same thing twice.** Work is cached by its computed *meaning*, not by filename. You share computations, not only derivations, so CI runs, clusters, and whole teams stop re-deriving identical results.
- **Every core, finally used.** Evaluation is lock-free parallel *by construction*, not bolted on afterward. Many-core machines stop idling while one thread chews through a build graph.
- **Software you can prove.** The substrate that builds your code can also verify mathematical claims about it. Build and proof, on one engine, speaking one language.
- **Reproducible builds for everyone.** Rootless, daemonless, no system-wide store. Your machine, your store, bit for bit, no privileged ceremony required.

The dream is a foundation for computing that is **reproducible, parallel, and verifiable**, and that belongs to everyone.

---

## A commons, not a product

`dnx` is public digital infrastructure, structured so it can stay that way:

- **Libre, always.** Free as in freedom, for everyone, forever. No paywalled core, no open core bait and switch.
- **For the public good.** Built to make computing more reproducible, efficient, and trustworthy, not to be captured or extracted from.
- **Sustainable in the open.** Developed transparently and funded as a commons, so it stays independent and free. AGPL3. These are constraints, not slogans.

---

## Sustaining dnx

`dnx` is and will remain libre. It is maintained as public infrastructure, so its longevity depends on **public support**, not on selling the software or trading away its independence. Sponsorship funds the open, full time work that turns the mathematics into something everyone can build on.

- **[💖 Sponsor the work](https://github.com/sponsors/vic)**, this directly sustains independent, commons-funded development.
- **Contribute** code, tests, docs, or real world use cases.
- **Adopt and report back**, production use and feedback shape what gets built next.

Support sustains the commons. It never buys influence over the open guarantee.

---

## Contributing

Issues, discussion, and pull requests are welcome. Because `dnx` rests on a precise computational model, core changes are reviewed against that model's properties: **confluence, optimality, soundness. Correctness first.**

## License

AGPL3, libre, and built to stay that way.
