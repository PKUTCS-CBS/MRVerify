# Formal Verification in Coq of MapReduce Applications within CBS

To rigorously discuss the reliability of cloud block storage (CBS), we develop a proof system and implement a verification tool for reasoning about the correctness of CBS data operations. The proof system has separation logic features, and the tool simplifies derivation while retaining mathematical rigor.

This proof system consists of the modeling language, heap predicates, triples, and reasoning rules. The modeling language represents CBS state and data operations, and the heap predicates describe the properties of a given CBS state. Besides, the triples specify the behavior of a program, and the reasoning rules supports verifying these triples.

We implement this proof system as a verification tool in Coq. Our tool can encode actual operations intuitively and verify specifications semi-automatically. The notations and type conversions in our tool improve the readability of the representation code. The automated proof scripts simplify the verifying process and skip the unnecessary details. 

Since the MapReduce framework plays an important role in the data analysis on CBS, it is necessary to ensure its correctness. The correctness of a program generally refers to that each input will produce the desired result. Verifying the correctness of the MapReduce application can prove the execution mechanism of MapReduce. It can also reason whether CBS, as a file system, can stably provide data support for the software running on it. Therefore, we represent and verify two MR applications, which can analyze the reliability of CBS from the application perspective to some extent.

## How We Reason about CBS Programs

First, code a function with the modeling language to represent an actual CBS data operation.

```Coq
Definition Copy_blk : val := 
  Fun bk :=
    Let ln := bget bk in    (* read the content of a block *)
      bcreate ln.           (* create a block *)
```

Second, specify the invocation of this function by a triple. This triple captures the system properties before and after the function invocation.

```Coq
Lemma triple_Copy_blk : forall (Hf:hfprop) (bp:bloc) (ln:listint),
  triple (Copy_blk bp)
    (\R[Hf, bp~b~>ln])
    (fun r => \exists bp', [r=bp'] \* \R[Hf,((bp'~b~>ln) \b* (bp~b~>ln))]).
```

Last, reason and prove such a triple using the proven reasoning rules. If this triple can be proved, it is sound since the reasoning rules are all sound. 

```Coq
Proof.
  intros. applys* triple_app_fun.             (* reason about invoking a funcation *)
  applys triple_let triple_bget. ext.         (* reason about reading a block *)
  applys triple_conseq_frame triple_bcreate.  (* reason about creating a new block *)
  rewrite* hstar_hempty_l'.                   (* rewrite the format and complete proof *)
  introv M. rewrite hstar_hexists in M.
  destruct M as (bp'&M). rewrite hstar_assoc, hstar_sep, hfstar_hempty_l in M.
  exists~ bp'.
Qed.
```

## Overview of Implementation

The Implementation of our proof system mainly consists the following parts:.

- Modeling Language  ——  Language.v
- Assertion Language  ——  CBS heap predicates (Himpl.v) + Internal heap predicates (InnerPre.v) 
- Specification Language  ——  Rules.v
- Verification of MapReduce applications ——  WordCount.v  and  InvertIndex.v
- Variable Notations —— Var.v 

In additions, our tool depends on a Coq standard library (TLC.v) and a definition of finite map (Fmap.v).

## Installation

The standard installation procedure requires Coq 8.8.0. If you do not have it yet, please [install Coq](https://github.com/coq/coq/releases/download/V8.8.0/coq-8.8.0-installer-windows-x86_64.exe) first.

To install the latest development version of our tool, use this:

```
  git clone https://github.com/PKUTCS-CSS/MRVerify.git
  cd MRVerify
  make
```

**Note** : Only English or Number is allowed in the file path!

## Replaying a sample proof

Then, you can load an example proof. There are several examples in the file Example.v. Just use the CoqIDE to open that file and check the proof. The success proof of a program will be as follows.

<img src="Ex.png" alt="avatar" style="zoom:40%;" />

