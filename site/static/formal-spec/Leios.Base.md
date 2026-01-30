## Leios.Base

This module defines core components for the base layer of Leios protocol.
It includes stake distribution, ranking blocks, and base layer abstractions.
<!--
<pre class="Agda"><a id="180" class="Symbol">{-#</a> <a id="184" class="Keyword">OPTIONS</a> <a id="192" class="Pragma">--safe</a> <a id="199" class="Symbol">#-}</a>
</pre>-->
<pre class="Agda"><a id="219" class="Keyword">open</a> <a id="224" class="Keyword">import</a> <a id="231" href="Leios.Prelude.html" class="Module">Leios.Prelude</a> <a id="245" class="Keyword">hiding</a> <a id="252" class="Symbol">(</a><a id="253" href="Class.Applicative.Core.html#506" class="Function Operator">_⊗_</a><a id="256" class="Symbol">)</a>
<a id="258" class="Keyword">open</a> <a id="263" class="Keyword">import</a> <a id="270" href="Leios.Abstract.html" class="Module">Leios.Abstract</a>
<a id="285" class="Keyword">open</a> <a id="290" class="Keyword">import</a> <a id="297" href="Leios.VRF.html" class="Module">Leios.VRF</a>

<a id="308" class="Keyword">open</a> <a id="313" class="Keyword">import</a> <a id="320" href="CategoricalCrypto.html" class="Module">CategoricalCrypto</a> <a id="338" class="Keyword">hiding</a> <a id="345" class="Symbol">(</a><a id="346" href="CategoricalCrypto.Machine.Core.html#2179" class="Function">id</a><a id="348" class="Symbol">;</a> <a id="350" href="CategoricalCrypto.Machine.Core.html#4922" class="Function Operator">_∘_</a><a id="353" class="Symbol">)</a>

<a id="356" class="Keyword">module</a> <a id="363" href="Leios.Base.html" class="Module">Leios.Base</a> <a id="374" class="Symbol">(</a><a id="375" href="Leios.Base.html#375" class="Bound">a</a> <a id="377" class="Symbol">:</a> <a id="379" href="Leios.Abstract.html#452" class="Record">LeiosAbstract</a><a id="392" class="Symbol">)</a> <a id="394" class="Symbol">(</a><a id="395" class="Keyword">open</a> <a id="400" href="Leios.Abstract.html#452" class="Module">LeiosAbstract</a> <a id="414" href="Leios.Base.html#375" class="Bound">a</a><a id="415" class="Symbol">)</a> <a id="417" class="Symbol">(</a><a id="418" href="Leios.Base.html#418" class="Bound">vrf&#39;</a> <a id="423" class="Symbol">:</a> <a id="425" href="Leios.VRF.html#878" class="Record">LeiosVRF</a> <a id="434" href="Leios.Base.html#375" class="Bound">a</a><a id="435" class="Symbol">)</a>
  <a id="439" class="Symbol">(</a><a id="440" class="Keyword">let</a> <a id="444" class="Keyword">open</a> <a id="449" href="Leios.VRF.html#878" class="Module">LeiosVRF</a> <a id="458" href="Leios.Base.html#418" class="Bound">vrf&#39;</a><a id="462" class="Symbol">)</a> <a id="464" class="Keyword">where</a>

<a id="471" class="Keyword">open</a> <a id="476" class="Keyword">import</a> <a id="483" href="Leios.Blocks.html" class="Module">Leios.Blocks</a> <a id="496" href="Leios.Base.html#375" class="Bound">a</a> <a id="498" class="Keyword">using</a> <a id="504" class="Symbol">(</a><a id="505" href="Leios.Blocks.html#1236" class="Function">EndorserBlock</a><a id="518" class="Symbol">;</a> <a id="520" href="Leios.Blocks.html#1007" class="Function">EBRef</a><a id="525" class="Symbol">)</a>

<a id="StakeDistr"></a><a id="528" href="Leios.Base.html#528" class="Function">StakeDistr</a> <a id="539" class="Symbol">:</a> <a id="541" href="Agda.Primitive.html#388" class="Primitive">Type</a>
<a id="546" href="Leios.Base.html#528" class="Function">StakeDistr</a> <a id="557" class="Symbol">=</a> <a id="559" href="Axiom.Set.TotalMap.html#574" class="Record">TotalMap</a> <a id="568" href="Leios.Abstract.html#512" class="Field">PoolID</a> <a id="575" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a>

<a id="578" class="Keyword">record</a> <a id="RankingBlock"></a><a id="585" href="Leios.Base.html#585" class="Record">RankingBlock</a> <a id="598" class="Symbol">:</a> <a id="600" href="Agda.Primitive.html#388" class="Primitive">Type</a> <a id="605" class="Keyword">where</a>
  <a id="613" class="Keyword">field</a> <a id="RankingBlock.txs"></a><a id="619" href="Leios.Base.html#619" class="Field">txs</a> <a id="623" class="Symbol">:</a> <a id="625" href="Agda.Builtin.List.html#147" class="Datatype">List</a> <a id="630" href="Leios.Abstract.html#488" class="Field">Tx</a>
        <a id="RankingBlock.announcedEB"></a><a id="641" href="Leios.Base.html#641" class="Field">announcedEB</a> <a id="653" class="Symbol">:</a> <a id="655" href="Agda.Builtin.Maybe.html#135" class="Datatype">Maybe</a> <a id="661" href="Leios.Abstract.html#632" class="Field">Hash</a>
        <a id="RankingBlock.ebCert"></a><a id="674" href="Leios.Base.html#674" class="Field">ebCert</a> <a id="681" class="Symbol">:</a> <a id="683" href="Agda.Builtin.Maybe.html#135" class="Datatype">Maybe</a> <a id="689" href="Leios.Abstract.html#656" class="Field">EBCert</a>

<a id="697" class="Keyword">record</a> <a id="BaseAbstract"></a><a id="704" href="Leios.Base.html#704" class="Record">BaseAbstract</a> <a id="717" class="Symbol">:</a> <a id="719" href="Agda.Primitive.html#388" class="Primitive">Type₁</a> <a id="725" class="Keyword">where</a>
  <a id="733" class="Keyword">field</a> <a id="BaseAbstract.Cert"></a><a id="739" href="Leios.Base.html#739" class="Field">Cert</a> <a id="744" class="Symbol">:</a> <a id="746" href="Agda.Primitive.html#388" class="Primitive">Type</a>
        <a id="BaseAbstract.VTy"></a><a id="759" href="Leios.Base.html#759" class="Field">VTy</a> <a id="763" class="Symbol">:</a> <a id="765" href="Agda.Primitive.html#388" class="Primitive">Type</a>
        <a id="BaseAbstract.initSlot"></a><a id="778" href="Leios.Base.html#778" class="Field">initSlot</a> <a id="787" class="Symbol">:</a> <a id="789" href="Leios.Base.html#759" class="Field">VTy</a> <a id="793" class="Symbol">→</a> <a id="795" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a>
        <a id="BaseAbstract.V-chkCerts"></a><a id="805" href="Leios.Base.html#805" class="Field">V-chkCerts</a> <a id="816" class="Symbol">:</a> <a id="818" href="Agda.Builtin.List.html#147" class="Datatype">List</a> <a id="823" href="Leios.VRF.html#909" class="Field">PubKey</a> <a id="830" class="Symbol">→</a> <a id="832" href="Leios.Blocks.html#1236" class="Function">EndorserBlock</a> <a id="846" href="Data.Product.Base.html#1618" class="Function Operator">×</a> <a id="848" href="Leios.Base.html#739" class="Field">Cert</a> <a id="853" class="Symbol">→</a> <a id="855" href="Agda.Builtin.Bool.html#173" class="Datatype">Bool</a>
        <a id="BaseAbstract.BaseNetwork"></a><a id="868" href="Leios.Base.html#868" class="Field">BaseNetwork</a> <a id="BaseAbstract.BaseAdv"></a><a id="880" href="Leios.Base.html#880" class="Field">BaseAdv</a> <a id="888" class="Symbol">:</a> <a id="890" href="CategoricalCrypto.Channel.Core.html#717" class="Record">Channel</a>
</pre>Type family for communicating with the base functionality.

The base layer can produce three types of outputs:
- Stake distribution information
- Empty response (no meaningful output)
- Base layer ledger contents
<pre class="Agda">  <a id="1125" class="Keyword">data</a> <a id="BaseAbstract.BaseIOF"></a><a id="1130" href="Leios.Base.html#1130" class="Datatype">BaseIOF</a> <a id="1138" class="Symbol">:</a> <a id="1140" href="CategoricalCrypto.Channel.Core.html#410" class="Datatype">Mode</a> <a id="1145" class="Symbol">→</a> <a id="1147" href="Agda.Primitive.html#388" class="Primitive">Type</a> <a id="1152" class="Keyword">where</a>
</pre>INIT: Initialize the base layer with a certificate validation function.

Parameters:
- (EndorserBlock × Cert → Bool): A validation function that checks
  whether an endorser block and certificate pair is valid.
  Returns True if the pair is valid, False otherwise.
<pre class="Agda">    <a id="BaseAbstract.BaseIOF.INIT"></a><a id="1439" href="Leios.Base.html#1439" class="InductiveConstructor">INIT</a>   <a id="1446" class="Symbol">:</a> <a id="1448" class="Symbol">(</a><a id="1449" href="Leios.Blocks.html#1236" class="Function">EndorserBlock</a> <a id="1463" href="Data.Product.Base.html#1618" class="Function Operator">×</a> <a id="1465" href="Leios.Base.html#739" class="Field">Cert</a> <a id="1470" class="Symbol">→</a> <a id="1472" href="Agda.Builtin.Bool.html#173" class="Datatype">Bool</a><a id="1476" class="Symbol">)</a> <a id="1478" class="Symbol">→</a> <a id="1480" href="Leios.Base.html#1130" class="Datatype">BaseIOF</a> <a id="1488" href="CategoricalCrypto.Channel.Core.html#430" class="InductiveConstructor">Out</a>
</pre>SUBMIT: Submit a ranking block to the base layer for processing.

Parameters:
- RankingBlock: A ranking block containing either an endorser block,
  a list of transactions, or both (using the These type constructor).
  This represents new content to be added to the ledger.
<pre class="Agda">    <a id="BaseAbstract.BaseIOF.SUBMIT"></a><a id="1782" href="Leios.Base.html#1782" class="InductiveConstructor">SUBMIT</a> <a id="1789" class="Symbol">:</a> <a id="1791" href="Leios.Base.html#585" class="Record">RankingBlock</a> <a id="1804" class="Symbol">→</a> <a id="1806" href="Leios.Base.html#1130" class="Datatype">BaseIOF</a> <a id="1814" href="CategoricalCrypto.Channel.Core.html#430" class="InductiveConstructor">Out</a>
</pre>FTCH-LDG: Request to fetch the current ledger state.

This input has no parameters and is used to query the current
state of the base layer ledger.
<pre class="Agda">    <a id="BaseAbstract.BaseIOF.FTCH-LDG"></a><a id="1982" href="Leios.Base.html#1982" class="InductiveConstructor">FTCH-LDG</a> <a id="1991" class="Symbol">:</a> <a id="1993" href="Leios.Base.html#1130" class="Datatype">BaseIOF</a> <a id="2001" href="CategoricalCrypto.Channel.Core.html#430" class="InductiveConstructor">Out</a>
</pre>The base layer can produce three types of outputs:
- Stake distribution information
- Empty response (no meaningful output)
- Base layer ledger contents

STAKE: Output containing the current stake distribution.

Parameters:
- StakeDistr: A total map from pool identifiers to their stake amounts (ℕ).
  This represents how stake is distributed across different pools
  in the system.
<pre class="Agda">    <a id="BaseAbstract.BaseIOF.STAKE"></a><a id="2404" href="Leios.Base.html#2404" class="InductiveConstructor">STAKE</a> <a id="2410" class="Symbol">:</a> <a id="2412" href="Leios.Base.html#528" class="Function">StakeDistr</a> <a id="2423" class="Symbol">→</a> <a id="2425" href="Leios.Base.html#1130" class="Datatype">BaseIOF</a> <a id="2433" href="CategoricalCrypto.Channel.Core.html#443" class="InductiveConstructor">In</a>
</pre>EMPTY: Empty output indicating no meaningful result.

This output is used when an operation completes successfully
but produces no data that needs to be returned to the caller.
<pre class="Agda">    <a id="BaseAbstract.BaseIOF.EMPTY"></a><a id="2629" href="Leios.Base.html#2629" class="InductiveConstructor">EMPTY</a> <a id="2635" class="Symbol">:</a> <a id="2637" href="Leios.Base.html#1130" class="Datatype">BaseIOF</a> <a id="2645" href="CategoricalCrypto.Channel.Core.html#443" class="InductiveConstructor">In</a>
</pre>BASE-LDG: Output containing the base layer ledger contents.

Parameters:
- List RankingBlock: A list of ranking blocks that constitute
  the current state of the base layer ledger. Each ranking block
  may contain endorser blocks, transactions, or both.
<pre class="Agda">    <a id="BaseAbstract.BaseIOF.BASE-LDG"></a><a id="2918" href="Leios.Base.html#2918" class="InductiveConstructor">BASE-LDG</a> <a id="2927" class="Symbol">:</a> <a id="2929" href="Agda.Builtin.List.html#147" class="Datatype">List</a> <a id="2934" href="Leios.Base.html#585" class="Record">RankingBlock</a> <a id="2947" class="Symbol">→</a> <a id="2949" href="Leios.Base.html#1130" class="Datatype">BaseIOF</a> <a id="2957" href="CategoricalCrypto.Channel.Core.html#443" class="InductiveConstructor">In</a>
</pre><pre class="Agda">  <a id="BaseAbstract.BaseIO"></a><a id="2974" href="Leios.Base.html#2974" class="Function">BaseIO</a> <a id="2981" class="Symbol">=</a> <a id="2983" href="CategoricalCrypto.Channel.Core.html#926" class="Function">simpleChannel</a> <a id="2997" href="Leios.Base.html#1130" class="Datatype">BaseIOF</a>

  <a id="3008" class="Keyword">record</a> <a id="BaseAbstract.BaseMachine"></a><a id="3015" href="Leios.Base.html#3015" class="Record">BaseMachine</a> <a id="3027" class="Symbol">:</a> <a id="3029" href="Agda.Primitive.html#388" class="Primitive">Type₁</a> <a id="3035" class="Keyword">where</a>
    <a id="3045" class="Keyword">field</a> <a id="3051" href="Leios.Base.html#3051" class="Field">m</a> <a id="3053" class="Symbol">:</a> <a id="3055" href="CategoricalCrypto.Machine.Core.html#875" class="Record">Machine</a> <a id="3063" href="Leios.Base.html#868" class="Field">BaseNetwork</a> <a id="3075" class="Symbol">(</a><a id="3076" href="Leios.Base.html#2974" class="Function">BaseIO</a> <a id="3083" href="CategoricalCrypto.Channel.Core.html#3393" class="Function Operator">⊗</a> <a id="3085" href="Leios.Base.html#880" class="Field">BaseAdv</a><a id="3092" class="Symbol">)</a>
          <a id="3104" class="Comment">-- IsBlockchain-m : IsBlockchain RankingBlock m -- this might be better</a>
          <a id="3186" class="Comment">-- TODO: how do we do this?</a>
          <a id="3224" class="Comment">-- SUBMIT-fun : IsFunction m (SUBMIT b) EMPTY</a>
          <a id="3280" class="Comment">-- FTCH-pfun : IsPureFunction m FTCH-LDG (BASE-LDG r)</a>
    <a id="3338" class="Keyword">open</a> <a id="3343" href="CategoricalCrypto.Machine.Core.html#875" class="Module">Machine</a> <a id="3351" href="Leios.Base.html#3051" class="Field">m</a> <a id="3353" class="Keyword">renaming</a> <a id="3362" class="Symbol">(</a><a id="3363" href="CategoricalCrypto.Machine.Core.html#997" class="Field">stepRel</a> <a id="3371" class="Symbol">to</a> <a id="3374" class="Field">_-⟦_/_⟧⇀_</a><a id="3383" class="Symbol">)</a> <a id="3385" class="Keyword">public</a>
</pre>