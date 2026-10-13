# Instructions for writing difficult-mathematics research prompts

**Version:** 2026-09-16, with modules F–G and sources R12–R14 added 2026-10-12  
**Audience:** The AI writing the research prompt—not, initially, the AI solving the mathematical problem.

## How to use this file

The user supplies this file and some background on a mathematical problem. Your job is to turn that material into **one self-contained, problem-specific prompt for a capable mathematical research AI**. Do not solve the problem instead, reproduce this guide, or produce a generic motivational prompt.

The default objective is a complete resolution of the user's exact problem. For a conjecture, a valid proof or a valid disproof is a successful mathematical outcome. Preserve any explicitly requested narrower objective, such as auditing a proof or settling one specified subproblem.

This is an evidence-informed design guide, not an experimentally validated universal optimum. Its central principle is:

> Be exact about the mathematical claim, evidence, and completion criteria; be selective about workflow requirements; leave room for genuinely different mathematics.

Sections 1–6 contain the core instructions. Section 7 contains optional modules: select only those relevant to the supplied task. The evidence and testing appendices are background for you and the user; do not copy them into the solver prompt.

## 1. Establish what is actually being asked

Read the supplied statement and relevant available attachments before writing the prompt. Preserve definitions, notation, theorem labels, filenames, and the distinction between the original problem and a proposed reduction. Inspect the portions needed to understand the target and current obstruction; do not spend the entire task rereading irrelevant material.

Separate the background into: definitions and assumptions; results with supplied proofs or verifiable references; claims inherited from earlier AI responses; conjectures or candidate lemmas; numerical evidence; and failed approaches with known obstructions. Do not silently promote an inherited claim to a proved theorem. Conversely, do not discard established work merely to start afresh.

Extract an explicit mathematical contract, including the relevant domain, hypotheses, quantifiers, requested conclusion, and meaning of success. When material, specify the order of quantifiers; parameter dependence of constants; norms and accuracy; deterministic versus probabilistic guarantees; admissible inputs and outputs; access model; and computational cost model. Include boundary, tie, or degeneracy conventions when they affect the claim. Do not append irrelevant technical conditions just to sound rigorous.

Resolve material inconsistencies from the supplied evidence where possible. Ask a targeted question only when an unrecoverable ambiguity changes the mathematics. Otherwise state any necessary interpretation explicitly. Do not invent a missing theorem, file content, parameter value, source, or available tool. When a resource will be supplied only to the eventual solver, name it as a resource to inspect, not as something you have verified.

For a conjecture, identify what its negation would require. A failure of the proposed proof route is not a counterexample. A conditional hardness theorem is not an unconditional impossibility result. A changed regularity assumption, rank allowance, oracle, or probability guarantee changes the problem unless a valid reduction connects it to the original.

## 2. Specify success without pressuring the solver to misreport

Make the requested endpoint precise: for example, a theorem with proof, an exact admissible counterexample, an algorithm with a proved guarantee and complexity bound, or a correctly qualified impossibility theorem. A numerical answer to a proof question is not enough.

Use language with this meaning, tailored to the problem:

> Pursue a complete resolution of the exact target. Do not stop merely because it is described as open, because a first approach fails, or because a useful intermediate lemma has been obtained. For a conjecture, investigate both proof and disproof without assuming the desired conclusion. Declare completion only when the argument establishes the original statement or its appropriate negation. If the available run ends unresolved, return the strongest rigorously supported result, its exact limitations, and the remaining mathematical obligation. An incomplete outcome must not be presented as a complete solution.

The fallback is a recovery protocol, not permission to aim only for an easy incremental result. If the user requests full completion, do not replace that objective with “prove any one lemma.” If the user requests an incremental task, do not expand it into an obligation to solve the whole research program.

Do not require the solver to assume a conjecture is true, a chosen technique must work, or a complete solution must be obtainable within this particular run. Avoid “return only a proof, never an incomplete answer” and similar restrictions on truthful reporting. Persistence is a search policy; correctness is a condition on the result.

## 3. Connect intermediate work to the original theorem

Require a compact **proof-obligation map** for a multi-stage problem. Each essential claim should have its exact statement, dependencies, current status, and proof or certificate location. A small table or a few paragraphs are sufficient; a large administrative registry is not a goal.

Most importantly, require the solver to explain why satisfying those obligations suffices for the original target. Distinguish necessary conditions from sufficient ones, an equivalent reformulation from a relaxation, and a solved template from exhaustive coverage. Expose any bridge lemma whose strength is essentially that of the original problem.

For example, proving a bound on cells C1, …, Ck establishes a bound on the full domain D only with a valid argument that these cells cover D, or another theorem that handles every omitted point. Finding an optimal-looking candidate does not prove global optimality. Counting completed certificates does not by itself measure distance to completion.

Treat the obligation map as revisable mathematics, not a mandated proof architecture. A valid structural theorem may replace an enormous case split. The solver may abandon or supersede the existing approach unless the user explicitly requires that approach; it must explain the replacement and preserve valid results.

On a continuation task, identify the actual unresolved bottleneck rather than simply saying “continue.” Do not inherit a previous AI's claim of near-completion without checking what still separates the saved result from the original theorem.

## 4. Give the solver an adaptable research process

### Start from the right mode

Choose from the user's context: new exploration, continuation of an existing argument, strategic reconsideration after repeated failures, or audit of a candidate proof. Do not impose the same workflow on all four.

For new exploration, request a small number of genuinely different mechanisms when useful, followed promptly by concrete mathematics. For continuation, prioritize the unresolved interfaces and preserve verified components. For a strategic reset, explicitly permit alternative formulations, alternative proof mechanisms, and counterexample searches in the original feasible class. For an audit, prioritize validity rather than generating an entirely new proof.

### Explore without locking onto the first attractive route

Ask for concrete advances: a proved lemma, construction, valid reduction, algorithmic invariant, exact counterexample, or targeted experiment that resolves a particular uncertainty. Broad lists of topics and repeated statements that an approach is promising are not substitutes.

A proposed route should identify its hardest necessary step and the next discriminating test. Prioritize the step most likely to decide whether the route can work, not merely the easiest lemma to write down. Test suspicious claims on relevant small, extremal, singular, or boundary cases. For a conjecture, some search should challenge the conjecture itself rather than only testing the current ansatz.

When a route stalls, record the precise obstruction and try a materially different mechanism. Reopen a failed route when a new observation addresses that obstruction. Avoid repeatedly renaming the same unproved lemma or generating variants that leave the same theorem-strength gap untouched.

Do not impose arbitrary quotas of approaches, experiments, or iterations. A brief comparison of a few routes may help; a productive proof should not be interrupted to satisfy a portfolio quota. Reserve effort for assembling and checking the final argument rather than spending the whole run exploring.

### Use genuine capabilities, not theatrical instructions

Adapt to the stated environment. Wording cannot grant browsing, code execution, formal verification, persistent storage, longer runtime, or additional agents. Do not claim that requesting those capabilities enables them.

When real parallel calls or subagents are available and the problem decomposes usefully, give each a precise subproblem, assumptions, expected mathematical output, and resource boundary. Preserve some separation between early approaches before sharing a favored answer. Assign integration responsibility explicitly. More agents are not automatically better.

Without such capabilities, use sequential exploration and a separate review pass. Do not describe simulated role dialogue as independent agent verification. Even genuine separate calls can share systematic errors; agreement is not proof.

Request a complete, checkable mathematical exposition and a concise record of useful decisions—not a transcript of private internal reasoning. Do not fill the prompt with instructions to think in a prescribed sequence or imitate a celebrated mathematician. Native reasoning settings and resource limits, when available, belong in the actual execution setup.

## 5. Require concrete checking and evidence-based repair

For each load-bearing new claim, ask what could make it false and how that possibility is addressed. Tailor the audit to the proof rather than pasting an encyclopedic checklist.

Review the original statement, quantifiers, hidden assumptions, exceptional cases, transformations, constants, and dependencies. Verify that imported theorems have the required hypotheses and that a cited result establishes the implication actually used. “Standard” is acceptable for a genuinely standard applicable fact, not for an unresolved bridge. Do not demand reproof of all established mathematics as a default.

Use literature search to check relevant primary sources and theorem applicability when browsing is available, not to replace the research task with a survey. When a source cannot be checked, distinguish a supplied citation or recalled result from one actually verified. Keep correctness and novelty separate: a correct argument may reproduce known work, and failure to find a reference does not establish originality.

When a candidate complete solution appears, temporarily prioritize validation and synthesis. Where feasible, give a fresh reviewer the exact problem, candidate proof, and necessary sources without instructing it that the candidate is correct. Ask it to evaluate neutrally: neither approve automatically nor invent objections to satisfy a demand to find errors.

Require substantive objections to identify the disputed step, the invalid inference or missing justification, and its consequence for the theorem. A suggested repair must itself be established. Assess the reviewer's criticism before accepting it; criticism from another model is not ground truth. Recheck modified steps and downstream dependencies after a repair.

Distinguish:

- A mathematical argument supplied in the response.
- A separate review that found no identified defect, with its actual scope.
- A computation or certificate checked by an identified procedure.
- A formally checked statement, with its assumptions and relationship to the original claim.

Do not conflate these forms of evidence. A persuasive self-assessment, repeated agreement, or numerical confidence score is not certification. Failure to find a counterexample is not proof.

## 6. Specify useful output and preserve an honest continuation state

Ask for the mathematical result before a narrative of the search. The final response should give the exact status and theorem or counterexample, the supporting argument, relevant verification and source details, and any deliverable files actually produced. A valid alternative proof need not follow the initially suggested structure.

The proof should be complete at the level appropriate to the research task: make new and delicate steps explicit, and state the applicability of standard imported results. Do not reward excessive length, polished exposition around a missing lemma, or repetition of the problem statement.

If unresolved, require a concise continuation record containing the strongest established statement; precisely what it does and does not imply; the remaining load-bearing obligation; failed routes and their concrete obstructions; relevant artifact locations; and the next discriminating mathematical action. Separate proved facts, conditional results, conjectures, and experimental observations. Do not replace this with a generic list of future research directions.

Do not promise background work or an eventual solution outside the available execution. Never fabricate commands, logs, citations, audits, or files. State unavailable checks rather than implying they ran.

## 7. Select only the relevant optional modules

### A. Computation, exact certificates, and formal proof

Use computation to test specific conjectures, find witnesses, explore structure, or verify a stated certificate. Specify the role of each computation: discovery, falsification, exhaustive verification, or certified bound. Record actual inputs, methods, and outcomes for checks relied upon.

High precision alone does not turn numerical evidence into proof. When certification requires it, convert candidates into rational or algebraic data, rigorously controlled interval bounds, exact symbolic identities, or independently checkable certificates. A finite search proves an infinite claim only after a valid finite reduction and exhaustive coverage argument. A single exact, admissible counterexample can disprove a universal claim.

Audit the mathematical meaning of the checker, not just whether it exits successfully. Check its inputs, domain coverage, arithmetic assumptions, and correspondence to the theorem. Preserve existing tests; do not weaken the verifier or redefine success to make a candidate pass. Separate exploratory code from the checker where practical.

Use formalization selectively when appropriate and actually available. A formal result must compile under the stated environment, have no admitted target-relevant gaps, and disclose relevant axioms or assumptions. Verify that the formal statement matches the intended mathematics; proving a weaker statement or assuming the difficult lemma does not settle the target. Partial formalization should be labeled precisely. Formal proof is not mandatory for every rigorous mathematical argument.

### B. Optimization, extremal problems, and finite case covers

Distinguish feasible candidates, local optima, necessary optimality conditions, and global bounds. Address existence or limiting behavior where needed. Check admissibility, normalization, equality cases, ties, boundaries, degeneracies, and the reversibility or direction of reductions.

For case decomposition, require a valid cover of the original domain, including newly active constraints and boundary descendants where relevant. Symmetry reduction requires the correct action and representative coverage. A relaxed problem may supply a valid upper bound without supplying an original-feasible witness; keep those uses separate. Do not require enumeration when a different global argument suffices.

### C. Algorithms, complexity, and lower bounds

Make access, input representation, output constraints, error measure, and resource accounting explicit. Include hidden preprocessing, auxiliary calls, precision costs, and randomness when material to the requested model. Do not move silently between explicit and oracle input or permit a larger output class than requested.

For adversarial lower bounds, inspect quantifier order, all permitted adaptive behavior, and consistency with a single valid instance when required. For conditional hardness, state the complexity assumption and prove the reduction with the needed parameter and guarantee preservation. Distinguish asymptotic constants from dependence on dimension, order, rank, or accuracy.

### D. Analysis, probability, and limiting arguments

Identify which exchanges of limits, sums, integrals, derivatives, or extrema require justification. Check the relevant regularity, compactness, measurability, integrability, and uniformity assumptions. Keep pointwise, uniform, almost-sure, in-probability, and expected guarantees distinct. Select only the issues the argument actually uses.

### E. Repository continuation and research artifacts

Name the real canonical manuscript and verification entry points supplied by the user. Instruct the solver to work there, not in an unrelated replacement project. Preserve valid earlier proofs and artifacts unless a concrete error is found; document corrections and their downstream consequences.

Read the saved mathematical status and run appropriate baseline checks when available. Use risk-based replay: inspect essential dependencies and changed components rather than spending every continuation run rebuilding everything. Record anything relied upon but not rerun.

Save new mathematics in the requested manuscript, relevant certificates and code alongside it, and actual replay commands and logs. Keep a compact status record with exact residual obligations and source locations so a new session can continue without reconstructing the entire conversation. Packaging and compilation do not establish mathematical correctness.

If requested, return an updated archive containing the actual modified files. Do not invent artifact paths, overwrite unrelated work, or claim an original external document was updated when only a local copy changed.

### F. Strategic reset after stagnation: eliciting genuinely new ideas

Use this module when several consecutive rounds return unresolved results built from ever finer local machinery without moving the central obstruction. Typical signs:
- the recommended "next discriminating action" is a larger version of the last computation;
- each round extends the solver's own earlier framework.

Continuing the thread with another narrow follow-up rarely helps. Instead:

- **Start a fresh context.** A long conversation anchors on its own earlier framing and becomes less stable. Give a new session a self-contained statement plus the state of knowledge. Label that state explicitly as a map of what is known and what not to rebuild, not as an architecture to continue.
- **Show what has been tried, and ask for something different.** List the approaches already used and the refuted shortcuts. Then ask for mechanisms substantially different from them. "Here are the known routes; propose a genuinely new one" is a more reliable trigger for novelty than an open-ended request [R14].
- **Structure the work as divergence, then selection, then depth.**
  - *Divergence:* ask for a handful of genuinely different mechanisms (a rough number is a guide, not a quota). Each comes with its core idea, why it survives the known refutations, its hardest step, and a cheap test that could kill it.
  - *Selection:* run the kill tests on the most promising few.
  - *Depth:* push the best survivor, and switch routes rather than polishing a stalled one. This keeps exploration from replacing concrete mathematics.
- **Offer cross-disciplinary seeds.** Give a short list of neighbouring fields or techniques that might transfer, explicitly marked as seeds rather than prescriptions. Cross-field transfer is one of the recurring sources of progress reported in research case studies [R12].
- **Suggest reformulations.** Examples:
  - strengthen the statement until it becomes inductive;
  - find the smallest special case that is genuinely open and new;
  - prove a weaker but new universal bound;
  - swap the roles of the objects, or reason backward;
  - argue about the whole process at once instead of step by step.
- **Frame the problem neutrally.** State the problem plainly. Emphasizing its fame or long-standing difficulty can make a model conservative; context de-identification has been reported to help [R12]. Never misstate the actual status.
- **Use generate-and-evaluate loops where an automatic evaluator exists.** Counterexample hunts suit a loop in which the model proposes candidates or search heuristics and code scores them, as in FunSearch/AlphaEvolve-style search [R8], [R13]. Offer real external compute only if it exists.
- **Check promising ideas.** Keep an adversarial review pass and code-checked claims; novelty does not replace verification.

### G. Practical lessons for long chat-based campaigns

- **Get answers inline.** Ask for final answers in the response text, and for code as plain readable source in blocks under about 15,000 characters, each with the SHA-256 of the assembled file. Never accept compressed, encoded or archived blobs. Transcribe, verify the hashes, and rerun certificates before accepting results.
- **Keep sandbox commands short.** Commands should stay well under five minutes and print progress notes; long-running commands cause stream interruptions.
- **Hand large computations outward.** For a decisive computation that is too big for the sandbox, ask for a runnable, checkpointable program with inputs, a resource estimate and the exact command. If a cluster is available, say so, and prefer programs that split into independent jobs.
- **Recover dead runs from saved work.** When a run dies or its stream stalls, ask for a report-only answer from the saved work rather than a redo. Separately confirm that the follow-up message was actually sent.
- **Mind the owner's machine.** Do not run multi-hour, all-core jobs on a personal machine without asking.

## 8. Assemble and edit the final solver prompt

Use a small number of clear sections, typically:

1. **Objective and exact mathematical statement.**
2. **Starting material, established results, and current obstruction.**
3. **Research freedom, priorities, and available resources.**
4. **Proof obligations and task-specific validation.**
5. **Required result, artifacts, and unresolved-run handoff.**

Write the important problem-specific content directly into those sections. Do not leave generic placeholders where the supplied material gives the answer. A supplied statement can be reproduced faithfully; a very large project can be referenced by exact locations plus a sufficient synopsis.

Keep procedural instructions compact. As an editorial starting point—not an evidence-based optimum—roughly 800–1,600 words of instructions beyond the necessary mathematical statement often provide ample room. A small task should be shorter; a delicate specification may need more. Remove duplicates and irrelevant modules rather than deleting crucial hypotheses to meet a length target.

Use examples only when a verified, relevant example clarifies the target, an expected certificate, or a known failure mode. Do not import unrelated solved examples or an elaborate reference proof that unintentionally restricts legitimate alternative methods. With an unspecified reasoning model, begin with a direct specification rather than a mandatory few-shot or chain-of-thought recipe.

Before returning the prompt, check that it:

- Asks for the user's actual problem and preserves all material mathematical constraints.
- Distinguishes established work from conjectural claims and connects local obligations to global success.
- Allows a materially different valid route and, for a conjecture, genuine disproof.
- Gives concrete verification requirements without treating model approval as truth.
- Contains no fictional capabilities, contradictory demands, or unsupported empirical promises.
- Aims at the requested endpoint while permitting accurate reporting of an unresolved outcome.

Return **one ready-to-use solver prompt**, not a discussion of how you would write it. Create a Markdown file when requested and file creation is available. Add separate reviewer or continuation prompts only when requested or when the user explicitly asks for a multi-call workflow.

---

## Appendix A. Research basis and limits

**For the prompt writer and human reader; do not append this bibliography to every solver prompt.** The operational recommendations above are a synthesis. None of these sources establishes that this complete guide is optimal for open mathematical research. Provider advice, controlled benchmark results, and research case reports are different kinds of evidence. Sources were checked on 2026-09-16.

**[R1] OpenAI, “Reasoning best practices.”** Official product guidance recommends direct instructions, explicit constraints, and clear delimiters; it discourages unnecessary prescribed chain-of-thought prompting for reasoning models. This is model-family guidance, not a controlled result about all mathematical research. Source: `https://developers.openai.com/api/docs/guides/reasoning-best-practices`.

**[R2] Anthropic, “Effective context engineering for AI agents” (2025).** Engineering guidance favors high-signal context and an appropriate level of specificity rather than brittle micromanagement or vagueness. This supports selective modules and relevant context, not the claim that the shortest prompt always wins. Source: `https://www.anthropic.com/engineering/effective-context-engineering-for-ai-agents`.

**[R3] OpenAI, First Proof submissions, Appendix A (2026).** The published appendix describes seed ideas, separate solution attempts, checking correctness and references, and revision. The original submissions were manually orchestrated; the programmatic framework was tried afterward. This is a relevant workflow example, not an ablation proving its wording or fixed iteration count optimal. Source: `https://cdn.openai.com/pdf/26177a73-3b75-4828-8c91-e8f1cf27aaa0/oai_first_proof.pdf`.

**[R4] “DeepSeekMath-V2: Towards Self-Verifiable Mathematical Reasoning” (2025), arXiv:2511.22570.** Includes proof-generation, verification, and refinement prompts, including reporting unresolved defects. Its results depend on specialized training and substantial inference procedures; copying a template does not reproduce those capabilities. Its competition-specific restrictions on using references should not automatically govern research mathematics. Source: `https://arxiv.org/abs/2511.22570`.

**[R5] Huang et al., “Large Language Models Cannot Self-Correct Reasoning Yet” (ICLR 2024), arXiv:2310.01798.** In the tested settings, intrinsic self-correction without external feedback often failed to improve reasoning and sometimes worsened it. This cautions against treating generic self-critique as validation; it does not establish that later models cannot benefit from revision. Source: `https://arxiv.org/abs/2310.01798`.

**[R6] “Reliable Fine-Grained Evaluation of Natural Language Math Proofs” (2025), arXiv:2510.13888.** Proof-evaluation experiments found model-dependent effects of strict versus flexible instructions and benefits from reference solutions and marking schemes. Those references are usually unavailable for unsolved problems, and the benchmark concerns competition proofs, not general research mathematics. This supports testing model-specific choices, not imposing one grading recipe universally. Source: `https://arxiv.org/abs/2510.13888`.

**[R7] Kim et al., “Towards a Science of Scaling Agent Systems,” version 3 (2026), arXiv:2512.08296v3.** Controlled agent-system comparisons found task- and architecture-dependent gains and losses from collaboration. These are not mathematical-research benchmarks. Conditional delegation rather than a fixed large agent count is an engineering extrapolation. Source: `https://arxiv.org/abs/2512.08296v3`.

**[R8] Romera-Paredes et al., “Mathematical discoveries from program search with large language models,” Nature 625, 468–475 (2024).** FunSearch combines generated programs with an evaluator in a search loop. It demonstrates a productive externally evaluated discovery setting, not a general proof-prompt recipe. Applicability depends on constructing the right evaluator. DOI: `10.1038/s41586-023-06924-6`.

**[R9] Anthropic, “Effective harnesses for long-running agents” (2025).** A coding-agent engineering account emphasizes persistent state, baseline checks, and explicit progress records across contexts. Applying that lesson to proof obligations and research archives is an extrapolation, not direct evidence from a mathematics trial. Source: `https://www.anthropic.com/engineering/effective-harnesses-for-long-running-agents`.

**[R10] Bubeck et al., “Early science acceleration experiments with GPT-5” (2025), arXiv:2511.16072.** Reports scientific and mathematical collaborations, including successes and limitations. Useful context for checking literature provenance and developing precise subproblems, but not a controlled comparison of prompting styles. Source: `https://arxiv.org/abs/2511.16072`.

**[R11] Phillip Kerger, “Closing the Oracle-Complexity Gap in Derivative-Free Convex Optimization: A Near-Quadratic Lower Bound from Exact Function Values,” arXiv:2607.13335v1 (2026), supplied paper.** Appendix A supplies a detailed model specification, concrete research tasks, approach registries, and targeted audits. These are valuable design examples. The reported successful run does not isolate the effect of its forceful wording or large-agent instructions. Page 27 also distinguishes the earlier result formalized in Lean from the stronger accuracy refinement; verification scope must match the claimed theorem.

**[R12] “Accelerating research with Gemini” (2026), arXiv:2602.03837.** Case studies on open problems in theoretical computer science, economics and physics, mostly obtained through interactive, conversational work rather than one-shot prompts. The recurring techniques named are iterative refinement, problem decomposition, cross-disciplinary knowledge transfer, adversarial review for subtle proof flaws, and neuro-symbolic loops in which the model writes and runs code to check derivations; secondary summaries also mention context de-identification. These are case reports, not controlled comparisons. Only the abstract and summaries were checked (2026-10-12). Source: `https://arxiv.org/abs/2602.03837`.

**[R13] Georgiev, Gómez-Serrano, Tao and Wagner, “Mathematical exploration and discovery at scale” (2025), arXiv:2511.02864.** AlphaEvolve on 67 problems: it rediscovered most best-known constructions and improved several, sometimes generalizing finite data into formulas, combined with separate proof systems. It supports generate-and-evaluate search when a programmatic scorer exists; it is not a recipe for proofs without an evaluator. Source: `https://arxiv.org/pdf/2511.02864`.

**[R14] Ye et al., “Assessing the Creativity of LLMs in Proposing Novel Solutions to Mathematical Problems” (AAAI 2025).** Asks models for solutions distinct from supplied known ones, from middle-school to olympiad level, and finds creative performance varies widely between models. It supports the "show known approaches, ask for a different one" pattern, but it evaluates rather than optimizes prompts. Source: `https://ojs.aaai.org/index.php/AAAI/article/view/34760`.

## Appendix B. Test the guide rather than trusting its style

To determine whether these instructions improve a particular model's work, compare problem-specific prompts generated from this guide with a simple exact-statement baseline and the previously used paper-style prompt. Hold the model version, starting files, tools, and overall inference budget comparable. Use fresh runs and multiple trials where practical; do not confuse more attempts with a wording improvement.

Include known-true tasks, false conjectures with checkable counterexamples, subtly flawed candidate proofs, and realistic saved research checkpoints. Prefer expert assessment blind to prompt condition, plus exact or formal checks where suitable. Evaluate the correctness of the claimed resolution, false-completion rate, removal of genuine mathematical bottlenecks, recoverability of unfinished work, and cost. Do not score only eloquence, length, confidence, or agreement.

Test important additions separately: counterexample search, external checks, fresh review, or persistent state. Use held-out tasks so repeated tailoring to one problem does not masquerade as a general improvement. A simpler prompt that performs better on these measures should replace a more elaborate one.
