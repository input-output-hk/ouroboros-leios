## Leios.Base

This module defines core components for the base layer of Leios protocol.
It includes stake distribution, ranking blocks, and base layer abstractions.
<!--
<pre class="Agda"><a id="180" class="Symbol">{-#</a> <a id="184" class="Keyword">OPTIONS</a> <a id="192" class="Pragma">--safe</a> <a id="199" class="Symbol">#-}</a>
</pre>-->
<pre class="Agda"><a id="219" class="Keyword">open</a> <a id="224" class="Keyword">import</a> <a id="231" href="Leios.Prelude.html" class="Module">Leios.Prelude</a> <a id="245" class="Keyword">hiding</a> <a id="252" class="Symbol">(</a><a id="253" href="Class.Applicative.Core.html#506" class="Function Operator">_⊗_</a><a id="256" class="Symbol">)</a>
<a id="258" class="Keyword">open</a> <a id="263" class="Keyword">import</a> <a id="270" href="Leios.Abstract.html" class="Module">Leios.Abstract</a>
<a id="285" class="Keyword">open</a> <a id="290" class="Keyword">import</a> <a id="297" href="Leios.VRF.html" class="Module">Leios.VRF</a>

<a id="308" class="Keyword">open</a> <a id="313" class="Keyword">import</a> <a id="320" href="CategoricalCrypto.html" class="Module">CategoricalCrypto</a> <a id="338" class="Keyword">hiding</a> <a id="345" class="Symbol">(</a><a id="346" href="CategoricalCrypto.Machine.Core.html#2174" class="Function">id</a><a id="348" class="Symbol">;</a> <a id="350" href="CategoricalCrypto.Machine.Core.html#5036" class="Function Operator">_∘_</a><a id="353" class="Symbol">)</a>

<a id="356" class="Keyword">module</a> <a id="363" href="Leios.Base.html" class="Module">Leios.Base</a>
  <a id="376" class="Symbol">(</a><a id="377" href="Leios.Base.html#377" class="Bound">a</a>    <a id="382" class="Symbol">:</a> <a id="384" href="Leios.Abstract.html#452" class="Record">LeiosAbstract</a><a id="397" class="Symbol">)</a> <a id="399" class="Symbol">(</a><a id="400" class="Keyword">open</a> <a id="405" href="Leios.Abstract.html#452" class="Module">LeiosAbstract</a> <a id="419" href="Leios.Base.html#377" class="Bound">a</a><a id="420" class="Symbol">)</a> 
  <a id="425" class="Symbol">(</a><a id="426" href="Leios.Base.html#426" class="Bound">vrf&#39;</a> <a id="431" class="Symbol">:</a> <a id="433" href="Leios.VRF.html#886" class="Record">LeiosVRF</a> <a id="442" href="Leios.Base.html#377" class="Bound">a</a>   <a id="446" class="Symbol">)</a> <a id="448" class="Symbol">(</a><a id="449" class="Keyword">open</a> <a id="454" href="Leios.VRF.html#886" class="Module">LeiosVRF</a> <a id="463" href="Leios.Base.html#426" class="Bound">vrf&#39;</a>  <a id="469" class="Symbol">)</a>
  <a id="473" class="Keyword">where</a>

<a id="480" class="Keyword">open</a> <a id="485" class="Keyword">import</a> <a id="492" href="Leios.Blocks.html" class="Module">Leios.Blocks</a> <a id="505" href="Leios.Base.html#377" class="Bound">a</a> <a id="507" class="Keyword">using</a> <a id="513" class="Symbol">(</a><a id="514" href="Leios.Blocks.html#1236" class="Function">EndorserBlock</a><a id="527" class="Symbol">;</a> <a id="529" href="Leios.Blocks.html#1007" class="Function">EBRef</a><a id="534" class="Symbol">)</a>

<a id="StakeDistr"></a><a id="537" href="Leios.Base.html#537" class="Function">StakeDistr</a> <a id="548" class="Symbol">:</a> <a id="550" href="Agda.Primitive.html#388" class="Primitive">Type</a>
<a id="555" href="Leios.Base.html#537" class="Function">StakeDistr</a> <a id="566" class="Symbol">=</a> <a id="568" href="Axiom.Set.TotalMap.html#574" class="Record">TotalMap</a> <a id="577" href="Leios.Abstract.html#512" class="Field">PoolID</a> <a id="584" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a>

<a id="587" class="Keyword">record</a> <a id="RankingBlock"></a><a id="594" href="Leios.Base.html#594" class="Record">RankingBlock</a> <a id="607" class="Symbol">:</a> <a id="609" href="Agda.Primitive.html#388" class="Primitive">Type</a> <a id="614" class="Keyword">where</a>
  <a id="622" class="Keyword">field</a> <a id="RankingBlock.txs"></a><a id="628" href="Leios.Base.html#628" class="Field">txs</a>         <a id="640" class="Symbol">:</a> <a id="642" href="Agda.Builtin.List.html#147" class="Datatype">List</a> <a id="647" href="Leios.Abstract.html#488" class="Field">Tx</a>
        <a id="RankingBlock.announcedEB"></a><a id="658" href="Leios.Base.html#658" class="Field">announcedEB</a> <a id="670" class="Symbol">:</a> <a id="672" href="Agda.Builtin.Maybe.html#135" class="Datatype">Maybe</a> <a id="678" href="Leios.Abstract.html#632" class="Field">Hash</a>
        <a id="RankingBlock.ebCert"></a><a id="691" href="Leios.Base.html#691" class="Field">ebCert</a>      <a id="703" class="Symbol">:</a> <a id="705" href="Agda.Builtin.Maybe.html#135" class="Datatype">Maybe</a> <a id="711" href="Leios.Abstract.html#656" class="Field">EBCert</a>
        <a id="RankingBlock.slot"></a><a id="726" href="Leios.Base.html#726" class="Field">slot</a>        <a id="738" class="Symbol">:</a> <a id="740" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a>

<a id="743" class="Keyword">record</a> <a id="BaseAbstract"></a><a id="750" href="Leios.Base.html#750" class="Record">BaseAbstract</a> <a id="763" class="Symbol">:</a> <a id="765" href="Agda.Primitive.html#388" class="Primitive">Type₁</a> <a id="771" class="Keyword">where</a>
  <a id="779" class="Keyword">field</a> <a id="BaseAbstract.Cert"></a><a id="785" href="Leios.Base.html#785" class="Field">Cert</a>        <a id="797" class="Symbol">:</a> <a id="799" href="Agda.Primitive.html#388" class="Primitive">Type</a>
        <a id="BaseAbstract.VTy"></a><a id="812" href="Leios.Base.html#812" class="Field">VTy</a>         <a id="824" class="Symbol">:</a> <a id="826" href="Agda.Primitive.html#388" class="Primitive">Type</a>
        <a id="BaseAbstract.initSlot"></a><a id="839" href="Leios.Base.html#839" class="Field">initSlot</a>    <a id="851" class="Symbol">:</a> <a id="853" href="Leios.Base.html#812" class="Field">VTy</a> <a id="857" class="Symbol">→</a> <a id="859" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a>
        <a id="BaseAbstract.V-chkCerts"></a><a id="869" href="Leios.Base.html#869" class="Field">V-chkCerts</a>  <a id="881" class="Symbol">:</a> <a id="883" href="Agda.Builtin.List.html#147" class="Datatype">List</a> <a id="888" href="Leios.VRF.html#917" class="Field">PubKey</a> <a id="895" class="Symbol">→</a> <a id="897" href="Leios.Blocks.html#1236" class="Function">EndorserBlock</a> <a id="911" href="Data.Product.Base.html#1618" class="Function Operator">×</a> <a id="913" href="Leios.Base.html#785" class="Field">Cert</a> <a id="918" class="Symbol">→</a> <a id="920" href="Agda.Builtin.Bool.html#173" class="Datatype">Bool</a>
        <a id="BaseAbstract.BaseAdv"></a><a id="933" href="Leios.Base.html#933" class="Field">BaseAdv</a>     <a id="945" class="Symbol">:</a> <a id="947" href="CategoricalCrypto.Channel.Core.html#710" class="Record">Channel</a>
        <a id="BaseAbstract.BaseMsg"></a><a id="963" href="Leios.Base.html#963" class="Field">BaseMsg</a>     <a id="975" class="Symbol">:</a> <a id="977" href="Agda.Primitive.html#388" class="Primitive">Type</a>
        <a id="990" class="Symbol">⦃</a> <a id="BaseAbstract.DecEq-BaseMsg"></a><a id="992" href="Leios.Base.html#992" class="Field">DecEq-BaseMsg</a> <a id="1006" class="Symbol">⦄</a> <a id="1008" class="Symbol">:</a> <a id="1010" href="Class.DecEq.Core.html#126" class="Record">DecEq</a> <a id="1016" href="Leios.Base.html#963" class="Field">BaseMsg</a>

  <a id="BaseAbstract.BaseNetwork"></a><a id="1027" href="Leios.Base.html#1027" class="Function">BaseNetwork</a> <a id="1039" class="Symbol">=</a> <a id="1041" href="CategoricalCrypto.Channel.Core.html#919" class="Function">simpleChannel</a> <a id="1055" class="Symbol">(λ</a> <a id="1058" href="Leios.Base.html#1058" class="Bound">_</a> <a id="1060" class="Symbol">→</a> <a id="1062" href="Agda.Builtin.List.html#147" class="Datatype">List</a> <a id="1067" href="Leios.Base.html#963" class="Field">BaseMsg</a><a id="1074" class="Symbol">)</a>
</pre>Type family for communicating with the base functionality.
<pre class="Agda">  <a id="1149" class="Keyword">data</a> <a id="BaseAbstract.BaseIOF"></a><a id="1154" href="Leios.Base.html#1154" class="Datatype">BaseIOF</a> <a id="1162" class="Symbol">:</a> <a id="1164" href="CategoricalCrypto.Channel.Core.html#403" class="Datatype">Mode</a> <a id="1169" class="Symbol">→</a> <a id="1171" href="Agda.Primitive.html#388" class="Primitive">Type</a> <a id="1176" class="Keyword">where</a>
</pre>INIT: Initialize the base layer with a certificate validation function.

Parameters:
- (EndorserBlock × Cert → Bool): A validation function that checks
  whether an endorser block and certificate pair is valid.
  Returns True if the pair is valid, False otherwise.
<pre class="Agda">    <a id="BaseAbstract.BaseIOF.INIT"></a><a id="1463" href="Leios.Base.html#1463" class="InductiveConstructor">INIT</a>   <a id="1470" class="Symbol">:</a> <a id="1472" class="Symbol">(</a><a id="1473" href="Leios.Blocks.html#1236" class="Function">EndorserBlock</a> <a id="1487" href="Data.Product.Base.html#1618" class="Function Operator">×</a> <a id="1489" href="Leios.Base.html#785" class="Field">Cert</a> <a id="1494" class="Symbol">→</a> <a id="1496" href="Agda.Builtin.Bool.html#173" class="Datatype">Bool</a><a id="1500" class="Symbol">)</a> <a id="1502" class="Symbol">→</a> <a id="1504" href="Leios.Base.html#1154" class="Datatype">BaseIOF</a> <a id="1512" href="CategoricalCrypto.Channel.Core.html#423" class="InductiveConstructor">Out</a>
</pre>SUBMIT: Submit a ranking block to the base layer for processing.

Parameters:
- RankingBlock: A ranking block containing either an endorser block,
  a list of transactions, or both (using the These type constructor).
  This represents new content to be added to the ledger.
<pre class="Agda">    <a id="BaseAbstract.BaseIOF.SUBMIT"></a><a id="1806" href="Leios.Base.html#1806" class="InductiveConstructor">SUBMIT</a> <a id="1813" class="Symbol">:</a> <a id="1815" href="Leios.Base.html#594" class="Record">RankingBlock</a> <a id="1828" class="Symbol">→</a> <a id="1830" href="Leios.Base.html#1154" class="Datatype">BaseIOF</a> <a id="1838" href="CategoricalCrypto.Channel.Core.html#423" class="InductiveConstructor">Out</a>
</pre>FTCH-LDG: Request to fetch the current ledger state.

This input has no parameters and is used to query the current
state of the base layer ledger.
<pre class="Agda">    <a id="BaseAbstract.BaseIOF.FTCH-LDG"></a><a id="2006" href="Leios.Base.html#2006" class="InductiveConstructor">FTCH-LDG</a> <a id="2015" class="Symbol">:</a> <a id="2017" href="Leios.Base.html#1154" class="Datatype">BaseIOF</a> <a id="2025" href="CategoricalCrypto.Channel.Core.html#423" class="InductiveConstructor">Out</a>
</pre>FTCH-SLOT: Request to fetch the current slot.

This input has no parameters and is used to query the current
slot of the base layer ledger.
<pre class="Agda">    <a id="BaseAbstract.BaseIOF.FTCH-SLOT"></a><a id="2185" href="Leios.Base.html#2185" class="InductiveConstructor">FTCH-SLOT</a> <a id="2195" class="Symbol">:</a> <a id="2197" href="Leios.Base.html#1154" class="Datatype">BaseIOF</a> <a id="2205" href="CategoricalCrypto.Channel.Core.html#423" class="InductiveConstructor">Out</a>
</pre>The base layer can produce four types of outputs:
- Stake distribution information
- Empty response (no meaningful output)
- Base layer ledger contents
- Curreent slot of the base layer

STAKE: Output containing the current stake distribution.

Parameters:
- StakeDistr: A total map from pool identifiers to their stake amounts (ℕ).
  This represents how stake is distributed across different pools
  in the system.
<pre class="Agda">    <a id="BaseAbstract.BaseIOF.STAKE"></a><a id="2641" href="Leios.Base.html#2641" class="InductiveConstructor">STAKE</a> <a id="2647" class="Symbol">:</a> <a id="2649" href="Leios.Base.html#537" class="Function">StakeDistr</a> <a id="2660" class="Symbol">→</a> <a id="2662" href="Leios.Base.html#1154" class="Datatype">BaseIOF</a> <a id="2670" href="CategoricalCrypto.Channel.Core.html#436" class="InductiveConstructor">In</a>
</pre>EMPTY: Empty output indicating no meaningful result.

This output is used when an operation completes successfully
but produces no data that needs to be returned to the caller.
<pre class="Agda">    <a id="BaseAbstract.BaseIOF.EMPTY"></a><a id="2866" href="Leios.Base.html#2866" class="InductiveConstructor">EMPTY</a> <a id="2872" class="Symbol">:</a> <a id="2874" href="Leios.Base.html#1154" class="Datatype">BaseIOF</a> <a id="2882" href="CategoricalCrypto.Channel.Core.html#436" class="InductiveConstructor">In</a>
</pre>BASE-LDG: Output containing the base layer ledger contents.

Parameters:
- List RankingBlock: A list of ranking blocks that constitute
  the current state of the base layer ledger. Each ranking block
  may contain endorser blocks, transactions, or both.
<pre class="Agda">    <a id="BaseAbstract.BaseIOF.BASE-LDG"></a><a id="3155" href="Leios.Base.html#3155" class="InductiveConstructor">BASE-LDG</a> <a id="3164" class="Symbol">:</a> <a id="3166" href="Agda.Builtin.List.html#147" class="Datatype">List</a> <a id="3171" href="Leios.Base.html#594" class="Record">RankingBlock</a> <a id="3184" class="Symbol">→</a> <a id="3186" href="Leios.Base.html#1154" class="Datatype">BaseIOF</a> <a id="3194" href="CategoricalCrypto.Channel.Core.html#436" class="InductiveConstructor">In</a>
</pre>SLOT: Output containing the current slot.

Parameters:
- ℕ: the current slot of the base machine. Should always be greater
or equal than the slot of the last processed block
<pre class="Agda">    <a id="BaseAbstract.BaseIOF.SLOT"></a><a id="3387" href="Leios.Base.html#3387" class="InductiveConstructor">SLOT</a> <a id="3392" class="Symbol">:</a> <a id="3394" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a> <a id="3396" class="Symbol">→</a> <a id="3398" href="Leios.Base.html#1154" class="Datatype">BaseIOF</a> <a id="3406" href="CategoricalCrypto.Channel.Core.html#436" class="InductiveConstructor">In</a>
</pre>
<pre class="Agda">  <a id="3424" class="Keyword">open</a> <a id="3429" class="Keyword">import</a> <a id="3436" href="Blockchain.Safety.html" class="Module">Blockchain.Safety</a>
  <a id="3456" class="Keyword">import</a> <a id="3463" href="Blockchain.IsBlockchain.html" class="Module">Blockchain.IsBlockchain</a> <a id="3487" class="Symbol">as</a> <a id="3490" class="Module">IsBC</a>
  <a id="3497" class="Keyword">open</a> <a id="3502" class="Keyword">import</a> <a id="3509" href="Data.Fin.Base.html" class="Module">Data.Fin.Base</a> <a id="3523" class="Keyword">using</a> <a id="3529" class="Symbol">(</a><a id="3530" href="Data.Fin.Base.html#2333" class="Function Operator">_↑ˡ_</a><a id="3534" class="Symbol">)</a>

  <a id="BaseAbstract.BaseIO"></a><a id="3539" href="Leios.Base.html#3539" class="Function">BaseIO</a> <a id="3546" class="Symbol">=</a> <a id="3548" href="CategoricalCrypto.Channel.Core.html#919" class="Function">simpleChannel</a> <a id="3562" href="Leios.Base.html#1154" class="Datatype">BaseIOF</a>

  <a id="3573" class="Keyword">record</a> <a id="BaseAbstract.BaseMachine"></a><a id="3580" href="Leios.Base.html#3580" class="Record">BaseMachine</a> <a id="3592" class="Symbol">:</a> <a id="3594" href="Agda.Primitive.html#388" class="Primitive">Type₂</a> <a id="3600" class="Keyword">where</a>
    <a id="3610" class="Keyword">field</a> <a id="3616" href="Leios.Base.html#3616" class="Field">n</a> <a id="3618" class="Symbol">:</a> <a id="3620" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a>

    <a id="3627" class="Keyword">open</a> <a id="3632" href="Blockchain.IsBlockchain.html" class="Module">IsBC</a> <a id="3637" class="Symbol">(</a><a id="3638" href="Data.Fin.Base.html#1132" class="Datatype">Fin</a> <a id="3642" href="Leios.Base.html#3616" class="Field">n</a><a id="3643" class="Symbol">)</a> <a id="3645" class="Keyword">public</a>

    <a id="3657" class="Keyword">field</a> <a id="3663" href="Leios.Base.html#3663" class="Field">m</a>             <a id="3677" class="Symbol">:</a> <a id="3679" href="CategoricalCrypto.Machine.Core.html#868" class="Record">Machine</a> <a id="3687" href="Leios.Base.html#1027" class="Function">BaseNetwork</a> <a id="3699" class="Symbol">(</a><a id="3700" href="Leios.Base.html#3539" class="Function">BaseIO</a> <a id="3707" href="CategoricalCrypto.Channel.Core.html#3360" class="Function Operator">⊗₀</a> <a id="3710" href="Leios.Base.html#933" class="Field">BaseAdv</a><a id="3717" class="Symbol">)</a>
          <a id="3729" href="Leios.Base.html#3729" class="Field">is-blockchain</a> <a id="3743" class="Symbol">:</a> <a id="3745" href="Blockchain.IsBlockchain.html#636" class="Record">IsBlockchain</a> <a id="3758" href="Leios.Base.html#594" class="Record">RankingBlock</a> <a id="3771" href="Leios.Base.html#3663" class="Field">m</a>

    <a id="3778" class="Keyword">open</a> <a id="3783" href="CategoricalCrypto.Machine.Core.html#868" class="Module">Machine</a> <a id="3791" href="Leios.Base.html#3663" class="Field">m</a> <a id="3793" class="Keyword">renaming</a> <a id="3802" class="Symbol">(</a><a id="3803" href="CategoricalCrypto.Machine.Core.html#990" class="Field">stepRel</a> <a id="3811" class="Symbol">to</a> <a id="3814" class="Field">_-⟦_/_⟧⇀_</a><a id="3823" class="Symbol">)</a> <a id="3825" class="Keyword">public</a>
</pre>