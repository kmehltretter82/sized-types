
Are "sized_types" like andreas abel did a dead end now ? Do they have a future ?
No, I don't think Andreas Abel's sized types are a dead end. But I do think their original incarnation in Agda has reached something of an impasse.
My assessment, as of October 2026, is:
As a theoretical idea: still powerful, elegant, and relevant.
As a practical feature in proof assistants: disappointing so far.
As an active research direction: definitely alive, including new work in 2026.
As the eventual standard mechanism for termination checking: much less certain.
The important distinction is between sized types as a principle and Agda's particular implementation.
1. What went wrong?
Abel's central idea was excellent: instead of checking termination solely by inspecting the syntax of recursive calls, express decreasingness in types.
For example, informally:
f
:
∀
i
.
  
L
i
s
t
i
(
A
)
→
B
f:∀i.List 
i
 (A)→B
A recursive call must consume a list with a strictly smaller size index.
This has some compelling advantages: modular termination checking, higher-order recursion, sophisticated nested datatypes, and a unified treatment of termination and productivity.
But three problems became serious.
First, soundness. Agda's sized types have known inconsistencies. In particular, the treatment of the infinite size permits something like
∞
<
∞
∞<∞
which undermines well-founded recursion. There are also other problematic interactions with the type system. Agda therefore disables sized types by default, and --safe rejects them. 

Agda 2.10.0 documentation
+2
Second, complexity. Sizes introduce subtyping, extra constraints, polymorphism over sizes, and interactions with dependent pattern matching and definitional equality. Integrating all this into a mature proof assistant is difficult.
Third, inference performance. Chan, Li, and Bowman explored sized types for Coq in their 2023 paper Is sized typing for Coq practical? They found severe performance problems when attempting fully automatic size inference while preserving compatibility with existing programs. Their conclusion was not that sized types are impossible, but that this particular integration strategy is impractical. 

Cambridge Core
These are genuine engineering and foundational obstacles, not merely a lack of interest.
2. But there have been important developments
Two pieces of work are particularly interesting.
2024: Abel and Nisht revisited type-based termination
Kanstantsin Nisht and Andreas Abel developed a new type-based termination checker for Agda, combining sized-type reasoning with the size-change principle.
The interesting part is that sizes could be inferred internally rather than appearing explicitly throughout users' programs. Their prototype also reported substantially better performance than the earlier Coq approach.
Unfortunately, the implementation encountered soundness problems. In May 2025, Abel moved the corresponding Agda pull request to the icebox, noting that nobody was working on resolving them.

The Agda Wiki
+2
This is a good illustration of both the continuing appeal of the idea and the difficulty of delivering it.
2026: A new consistency result
Constructing (Co)inductive Types via Large Sizes
Bastiaan Laarakker, Daniël Otten, and Benno van den Berg, FSCD 2026.
This paper is particularly relevant to your question.
The authors investigate a different foundation using a large type of sizes and parametric quantification over sizes. They construct inductive and coinductive types within the resulting theory and justify consistency through a realizability model involving an uncountable ordinal.
This is not a production-ready replacement for Agda's sized types, but it provides substantial evidence that the mathematical approach itself is not fundamentally broken. 

drops.dagstuhl.de
3. Where I think the future lies
I suspect there are two somewhat different futures.
Explicit sized types may remain a specialized but valuable tool, particularly for higher-order recursion, mixed induction/coinduction, and programming with infinite structures. They provide useful information that ordinary structural termination checking cannot always express.
Implicit type-based termination analysis may have the greater practical potential. Rather than exposing Size, Size<, and size-polymorphic signatures to programmers, a checker could reconstruct enough size information to establish termination compositionally.
That second direction is particularly attractive because it could retain much of Abel's conceptual contribution without requiring an entirely new programming style.
However, sized types also face serious competition from guarded recursion, clock quantification, conventional well-founded recursion, and increasingly sophisticated termination checkers. Guarded type theories are particularly interesting for productivity and coinduction, although they do not simply subsume every application of sized types.
4. Is this still a worthwhile research direction?
Yes, particularly if the goal is to improve on Abel's framework rather than merely reproduce it.
I see a few genuinely open questions: Can we provide a clean, fully consistent dependent theory with expressive size polymorphism? Can we integrate size-based termination into existing proof assistants without expensive global inference? Can we combine sized typing with guarded recursion or modern cubical type theory in a principled way?
My prediction is that sized types are unlikely to replace structural termination checking wholesale. Instead, their most successful ideas will probably become part of more general, hybrid termination and productivity systems.
And I wouldn't be surprised if, ten years from now, we find that Abel's most lasting contribution was not Agda's Size datatype, but the deeper idea that termination information should be compositional and reflected in types rather than recovered entirely from syntax.
That idea seems far from exhausted.
One distinction I'd be interested in exploring further is whether you mean sized types as a foundation for dependent type theory, or sized types as a practical mechanism for automatic termination and productivity checking. My outlook is significantly more optimistic about the former than about fully automatic inference in the latter.



