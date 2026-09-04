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
  <a id="622" class="Keyword">field</a> <a id="RankingBlock.announcedEB"></a><a id="628" href="Leios.Base.html#628" class="Field">announcedEB</a> <a id="640" class="Symbol">:</a> <a id="642" href="Agda.Builtin.Maybe.html#135" class="Datatype">Maybe</a> <a id="648" href="Leios.Abstract.html#632" class="Field">Hash</a>
        <a id="RankingBlock.txsOrEbCert"></a><a id="661" href="Leios.Base.html#661" class="Field">txsOrEbCert</a> <a id="673" class="Symbol">:</a> <a id="675" href="Agda.Builtin.List.html#147" class="Datatype">List</a> <a id="680" href="Leios.Abstract.html#488" class="Field">Tx</a> <a id="683" href="Data.Sum.Base.html#625" class="Datatype Operator">⊎</a> <a id="685" href="Leios.Abstract.html#656" class="Field">EBCert</a>

<a id="693" class="Keyword">record</a> <a id="BaseAbstract"></a><a id="700" href="Leios.Base.html#700" class="Record">BaseAbstract</a> <a id="713" class="Symbol">:</a> <a id="715" href="Agda.Primitive.html#388" class="Primitive">Type₁</a> <a id="721" class="Keyword">where</a>
  <a id="729" class="Keyword">field</a> <a id="BaseAbstract.Cert"></a><a id="735" href="Leios.Base.html#735" class="Field">Cert</a>        <a id="747" class="Symbol">:</a> <a id="749" href="Agda.Primitive.html#388" class="Primitive">Type</a>
        <a id="BaseAbstract.VTy"></a><a id="762" href="Leios.Base.html#762" class="Field">VTy</a>         <a id="774" class="Symbol">:</a> <a id="776" href="Agda.Primitive.html#388" class="Primitive">Type</a>
        <a id="BaseAbstract.initSlot"></a><a id="789" href="Leios.Base.html#789" class="Field">initSlot</a>    <a id="801" class="Symbol">:</a> <a id="803" href="Leios.Base.html#762" class="Field">VTy</a> <a id="807" class="Symbol">→</a> <a id="809" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a>
        <a id="BaseAbstract.V-chkCerts"></a><a id="819" href="Leios.Base.html#819" class="Field">V-chkCerts</a>  <a id="831" class="Symbol">:</a> <a id="833" href="Agda.Builtin.List.html#147" class="Datatype">List</a> <a id="838" href="Leios.VRF.html#917" class="Field">PubKey</a> <a id="845" class="Symbol">→</a> <a id="847" href="Leios.Blocks.html#1236" class="Function">EndorserBlock</a> <a id="861" href="Data.Product.Base.html#1618" class="Function Operator">×</a> <a id="863" href="Leios.Base.html#735" class="Field">Cert</a> <a id="868" class="Symbol">→</a> <a id="870" href="Agda.Builtin.Bool.html#173" class="Datatype">Bool</a>
        <a id="BaseAbstract.BaseAdv"></a><a id="883" href="Leios.Base.html#883" class="Field">BaseAdv</a>     <a id="895" class="Symbol">:</a> <a id="897" href="CategoricalCrypto.Channel.Core.html#710" class="Record">Channel</a>
        <a id="BaseAbstract.BaseMsg"></a><a id="913" href="Leios.Base.html#913" class="Field">BaseMsg</a>     <a id="925" class="Symbol">:</a> <a id="927" href="Agda.Primitive.html#388" class="Primitive">Type</a>
        <a id="940" class="Symbol">⦃</a> <a id="BaseAbstract.DecEq-BaseMsg"></a><a id="942" href="Leios.Base.html#942" class="Field">DecEq-BaseMsg</a> <a id="956" class="Symbol">⦄</a> <a id="958" class="Symbol">:</a> <a id="960" href="Class.DecEq.Core.html#126" class="Record">DecEq</a> <a id="966" href="Leios.Base.html#913" class="Field">BaseMsg</a>

  <a id="BaseAbstract.BaseNetwork"></a><a id="977" href="Leios.Base.html#977" class="Function">BaseNetwork</a> <a id="989" class="Symbol">=</a> <a id="991" href="CategoricalCrypto.Channel.Core.html#919" class="Function">simpleChannel</a> <a id="1005" class="Symbol">(λ</a> <a id="1008" href="Leios.Base.html#1008" class="Bound">_</a> <a id="1010" class="Symbol">→</a> <a id="1012" href="Agda.Builtin.List.html#147" class="Datatype">List</a> <a id="1017" href="Leios.Base.html#913" class="Field">BaseMsg</a><a id="1024" class="Symbol">)</a>
</pre>Type family for communicating with the base functionality.
<pre class="Agda">  <a id="1099" class="Keyword">data</a> <a id="BaseAbstract.BaseIOF"></a><a id="1104" href="Leios.Base.html#1104" class="Datatype">BaseIOF</a> <a id="1112" class="Symbol">:</a> <a id="1114" href="CategoricalCrypto.Channel.Core.html#403" class="Datatype">Mode</a> <a id="1119" class="Symbol">→</a> <a id="1121" href="Agda.Primitive.html#388" class="Primitive">Type</a> <a id="1126" class="Keyword">where</a>
</pre>INIT: Initialize the base layer with a certificate validation function.

Parameters:
- (EndorserBlock × Cert → Bool): A validation function that checks
  whether an endorser block and certificate pair is valid.
  Returns True if the pair is valid, False otherwise.
<pre class="Agda">    <a id="BaseAbstract.BaseIOF.INIT"></a><a id="1413" href="Leios.Base.html#1413" class="InductiveConstructor">INIT</a>   <a id="1420" class="Symbol">:</a> <a id="1422" class="Symbol">(</a><a id="1423" href="Leios.Blocks.html#1236" class="Function">EndorserBlock</a> <a id="1437" href="Data.Product.Base.html#1618" class="Function Operator">×</a> <a id="1439" href="Leios.Base.html#735" class="Field">Cert</a> <a id="1444" class="Symbol">→</a> <a id="1446" href="Agda.Builtin.Bool.html#173" class="Datatype">Bool</a><a id="1450" class="Symbol">)</a> <a id="1452" class="Symbol">→</a> <a id="1454" href="Leios.Base.html#1104" class="Datatype">BaseIOF</a> <a id="1462" href="CategoricalCrypto.Channel.Core.html#423" class="InductiveConstructor">Out</a>
</pre>SUBMIT: Submit a ranking block to the base layer for processing.

Parameters:
- RankingBlock: A ranking block containing either an endorser block,
  a list of transactions, or both (using the These type constructor).
  This represents new content to be added to the ledger.
<pre class="Agda">    <a id="BaseAbstract.BaseIOF.SUBMIT"></a><a id="1756" href="Leios.Base.html#1756" class="InductiveConstructor">SUBMIT</a> <a id="1763" class="Symbol">:</a> <a id="1765" href="Leios.Base.html#594" class="Record">RankingBlock</a> <a id="1778" class="Symbol">→</a> <a id="1780" href="Leios.Base.html#1104" class="Datatype">BaseIOF</a> <a id="1788" href="CategoricalCrypto.Channel.Core.html#423" class="InductiveConstructor">Out</a>
</pre>FTCH-LDG: Request to fetch the current ledger state.

This input has no parameters and is used to query the current
state of the base layer ledger.
<pre class="Agda">    <a id="BaseAbstract.BaseIOF.FTCH-LDG"></a><a id="1956" href="Leios.Base.html#1956" class="InductiveConstructor">FTCH-LDG</a> <a id="1965" class="Symbol">:</a> <a id="1967" href="Leios.Base.html#1104" class="Datatype">BaseIOF</a> <a id="1975" href="CategoricalCrypto.Channel.Core.html#423" class="InductiveConstructor">Out</a>
</pre>FTCH-SLOT: Request to fetch the current slot.

This input has no parameters and is used to query the current
slot of the base layer ledger.
<pre class="Agda">    <a id="BaseAbstract.BaseIOF.FTCH-SLOT"></a><a id="2135" href="Leios.Base.html#2135" class="InductiveConstructor">FTCH-SLOT</a> <a id="2145" class="Symbol">:</a> <a id="2147" href="Leios.Base.html#1104" class="Datatype">BaseIOF</a> <a id="2155" href="CategoricalCrypto.Channel.Core.html#423" class="InductiveConstructor">Out</a>
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
<pre class="Agda">    <a id="BaseAbstract.BaseIOF.STAKE"></a><a id="2591" href="Leios.Base.html#2591" class="InductiveConstructor">STAKE</a> <a id="2597" class="Symbol">:</a> <a id="2599" href="Leios.Base.html#537" class="Function">StakeDistr</a> <a id="2610" class="Symbol">→</a> <a id="2612" href="Leios.Base.html#1104" class="Datatype">BaseIOF</a> <a id="2620" href="CategoricalCrypto.Channel.Core.html#436" class="InductiveConstructor">In</a>
</pre>EMPTY: Empty output indicating no meaningful result.

This output is used when an operation completes successfully
but produces no data that needs to be returned to the caller.
<pre class="Agda">    <a id="BaseAbstract.BaseIOF.EMPTY"></a><a id="2816" href="Leios.Base.html#2816" class="InductiveConstructor">EMPTY</a> <a id="2822" class="Symbol">:</a> <a id="2824" href="Leios.Base.html#1104" class="Datatype">BaseIOF</a> <a id="2832" href="CategoricalCrypto.Channel.Core.html#436" class="InductiveConstructor">In</a>
</pre>BASE-LDG: Output containing the base layer ledger contents.

Parameters:
- List RankingBlock: A list of ranking blocks that constitute
  the current state of the base layer ledger. Each ranking block
  may contain endorser blocks, transactions, or both.
<pre class="Agda">    <a id="BaseAbstract.BaseIOF.BASE-LDG"></a><a id="3105" href="Leios.Base.html#3105" class="InductiveConstructor">BASE-LDG</a> <a id="3114" class="Symbol">:</a> <a id="3116" href="Agda.Builtin.List.html#147" class="Datatype">List</a> <a id="3121" href="Leios.Base.html#594" class="Record">RankingBlock</a> <a id="3134" class="Symbol">→</a> <a id="3136" href="Leios.Base.html#1104" class="Datatype">BaseIOF</a> <a id="3144" href="CategoricalCrypto.Channel.Core.html#436" class="InductiveConstructor">In</a>
</pre>SLOT: Output containing the current slot.

Parameters:
- ℕ: the current slot of the base machine. Should always be greater
or equal than the slot of the last processed block
<pre class="Agda">    <a id="BaseAbstract.BaseIOF.SLOT"></a><a id="3337" href="Leios.Base.html#3337" class="InductiveConstructor">SLOT</a> <a id="3342" class="Symbol">:</a> <a id="3344" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a> <a id="3346" class="Symbol">→</a> <a id="3348" href="Leios.Base.html#1104" class="Datatype">BaseIOF</a> <a id="3356" href="CategoricalCrypto.Channel.Core.html#436" class="InductiveConstructor">In</a>
</pre>
<pre class="Agda">  <a id="3374" class="Keyword">open</a> <a id="3379" class="Keyword">import</a> <a id="3386" href="Blockchain.Safety.html" class="Module">Blockchain.Safety</a>
  <a id="3406" class="Keyword">import</a> <a id="3413" href="Blockchain.IsBlockchain.html" class="Module">Blockchain.IsBlockchain</a> <a id="3437" class="Symbol">as</a> <a id="3440" class="Module">IsBC</a>
  <a id="3447" class="Keyword">open</a> <a id="3452" class="Keyword">import</a> <a id="3459" href="Data.Fin.Base.html" class="Module">Data.Fin.Base</a> <a id="3473" class="Keyword">using</a> <a id="3479" class="Symbol">(</a><a id="3480" href="Data.Fin.Base.html#2333" class="Function Operator">_↑ˡ_</a><a id="3484" class="Symbol">)</a>

  <a id="BaseAbstract.BaseIO"></a><a id="3489" href="Leios.Base.html#3489" class="Function">BaseIO</a> <a id="3496" class="Symbol">=</a> <a id="3498" href="CategoricalCrypto.Channel.Core.html#919" class="Function">simpleChannel</a> <a id="3512" href="Leios.Base.html#1104" class="Datatype">BaseIOF</a>

  <a id="3523" class="Keyword">record</a> <a id="BaseAbstract.BaseMachine"></a><a id="3530" href="Leios.Base.html#3530" class="Record">BaseMachine</a> <a id="3542" class="Symbol">:</a> <a id="3544" href="Agda.Primitive.html#388" class="Primitive">Type₂</a> <a id="3550" class="Keyword">where</a>
    <a id="3560" class="Keyword">field</a> <a id="3566" href="Leios.Base.html#3566" class="Field">n</a> <a id="3568" class="Symbol">:</a> <a id="3570" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a>

    <a id="3577" class="Keyword">open</a> <a id="3582" href="Blockchain.IsBlockchain.html" class="Module">IsBC</a> <a id="3587" class="Symbol">(</a><a id="3588" href="Data.Fin.Base.html#1132" class="Datatype">Fin</a> <a id="3592" href="Leios.Base.html#3566" class="Field">n</a><a id="3593" class="Symbol">)</a> <a id="3595" class="Keyword">public</a>

    <a id="3607" class="Keyword">field</a> <a id="3613" href="Leios.Base.html#3613" class="Field">m</a>             <a id="3627" class="Symbol">:</a> <a id="3629" href="CategoricalCrypto.Machine.Core.html#868" class="Record">Machine</a> <a id="3637" href="Leios.Base.html#977" class="Function">BaseNetwork</a> <a id="3649" class="Symbol">(</a><a id="3650" href="Leios.Base.html#3489" class="Function">BaseIO</a> <a id="3657" href="CategoricalCrypto.Channel.Core.html#3360" class="Function Operator">⊗₀</a> <a id="3660" href="Leios.Base.html#883" class="Field">BaseAdv</a><a id="3667" class="Symbol">)</a>
          <a id="3679" href="Leios.Base.html#3679" class="Field">is-blockchain</a> <a id="3693" class="Symbol">:</a> <a id="3695" href="Blockchain.IsBlockchain.html#636" class="Record">IsBlockchain</a> <a id="3708" href="Leios.Base.html#594" class="Record">RankingBlock</a> <a id="3721" href="Leios.Base.html#3613" class="Field">m</a>

    <a id="3728" class="Keyword">open</a> <a id="3733" href="CategoricalCrypto.Machine.Core.html#868" class="Module">Machine</a> <a id="3741" href="Leios.Base.html#3613" class="Field">m</a> <a id="3743" class="Keyword">renaming</a> <a id="3752" class="Symbol">(</a><a id="3753" href="CategoricalCrypto.Machine.Core.html#990" class="Field">stepRel</a> <a id="3761" class="Symbol">to</a> <a id="3764" class="Field">_-⟦_/_⟧⇀_</a><a id="3773" class="Symbol">)</a> <a id="3775" class="Keyword">public</a>
</pre>