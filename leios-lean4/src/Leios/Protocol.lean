import Leios.BLS
import Leios.FFD
import Leios.Messages
import Leios.Vote
import Leios.VRF

open Leios


namespace Leios.Protocol


structure Parameters where
  L : Nat
  lambda : Nat
  mu : Nat
  fIB : Float
  fEB : Float
deriving Repr


structure Leios where
  parameters : Parameters
  ffdParameters : FFD.Parameters
  voteParameters : Vote.Parameters
  blsParam : BLS.Param
  vrfVariables : VRF.Variables
  vrfSimulator : S
  ffdIB : FFD.Variables Messages.IB.Header Messages.IB.Body
  ffdEB : FFD.Variables Messages.EB Unit
  ffdVote : FFD.Variables Messages.VoteEB Unit
  ffdAdversaryIB : A_IB
  ffdAdversaryEB : A_EB
  ffdAdversaryVote : A_Vote


/-
General
-/


/-
Initialization: Upon receiving (INIT,𝑉 ), store 𝑉 and create and register the IB/EB lottery and
voting keys with the key registration functionality, which as a response outputs the
full public key list. The list is used to generate predicate 𝑉chkCerts. Send input (INIT,𝑉chkCerts)
to the base protocol; receive (Stake, SD) from the base protocol and store SD (to be used for the
IB/EB lottery and voting).
-/

def Initialization [MonadStateOf Leios m] : m Unit :=
  sorry


/-
Network and ledger: At the beginning of each slot:

(1) Fetch new messages (IBs, EBs, and votes) from 𝐹FFD and discard invalid ones (cf.
Section 3.2).

(2) Compute the ledger by following the EB-(EB-)∗-IB references in the base ledger in
order and concatenating the payloads in the IBs up to the point of the first IB with an
non-downloaded body (if any); sanitize the ledger based on 𝑉 , as detailed in
Section 3.1.7.

(3) Output the resulting ledger upon receiving command FTCH-LDG.
-/

def NetworkAndLedger [MonadStateOf Leios m] : m Unit :=
  sorry


/-
Base chain: In each slot 𝑠:

(1) Upon (SUBMIT, txs), store transactions txs.

(2) Pick an arbitrary Vote2-certified EB EB from slice𝐿 (𝑠, 2) and send (SUBMIT, EB) to the
base protocol; if there are no such EBs, submit (SUBMIT, txs) for the (most recently)
stored txs.
-/

def BaseChain [MonadStateOf Leios m] : m Unit :=
  sorry


/-
Protocol Roles

In every slot 𝑠, each party 𝑃 executes the following roles:
-/


/-
IB Role:

(1) Check if eligible to produce an IB in slot 𝑠. If so, let 𝜋 be the corresponding proof;
otherwise, exit the procedure.

(2) Let txs be the (most recently stored) transactions. Set IB := (ℎ, txs) where
ℎ := (𝑠, 𝑃, 𝜋, 𝑥, 𝜎), where 𝑥 is the hash of 𝑏 and 𝜎 is a signature of (the rest of) ℎ under
𝑃’s key in MI.

(3) Diffuse IB via 𝐹FFD.
-/

def RoleIB [MonadStateOf Leios m] : m Unit :=
  sorry


/-
EB Role:

(1) Check if eligible to produce an EB in slot 𝑠. If so, let 𝜋 be the corresponding proof;
otherwise, exit the procedure.

(2) Link role: set 𝐿I to be all (completely downloaded) IBs from slice𝐿 (𝑠, 𝜆 + 1).

(3) Endorse role: set 𝐿E to be all Vote1-certified EBs from slice𝐿 (𝑠, 𝜇 + 2).

(4) Diffuse EB := (𝑠, 𝑃, 𝜋, 𝐿I, 𝐿E, 𝜎) via 𝐹FFD, where 𝜎 is a signature of (the rest of) EB
under 𝑃’s key in MI.
-/

def RoleEB [MonadStateOf Leios m] : m Unit :=
  sorry


/-
Vote-1 Role:

(1) Check if eligible to produce Vote1-vote in slot 𝑠.

(2) Create a vote for each EB from slice𝐿 (𝑠, 𝜇 + 1) for which all referenced IBs
are fully downloaded.

(3) Diffuse the votes via 𝐹FFD.
-/

def RoleVote1 [MonadStateOf Leios m] : m Unit :=
  sorry


/-
Vote-2 Role:

(1) Check if eligible to produce Vote2-vote in slot 𝑠.

(2) Create vote for each EB from slice𝐿 (𝑠, 1) that references (i) a majority of all seen
Vote1-certified EBs from slice𝐿 (𝑠, 𝜇 + 3) and (ii) no other EBs.

(3) Diffuse the votes via 𝐹FFD
-/

def RoleVote2 [MonadStateOf Leios m] : m Unit :=
  sorry


end Leios.Protocol
