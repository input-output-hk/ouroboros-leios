## Leios.Base

This module defines core components for the base layer of Leios protocol.
It includes stake distribution, ranking blocks, and base layer abstractions.
<!--
<pre class="Agda"><a id="180" class="Symbol">{-#</a> <a id="184" class="Keyword">OPTIONS</a> <a id="192" class="Pragma">--safe</a> <a id="199" class="Symbol">#-}</a>
</pre>-->
<pre class="Agda"><a id="219" class="Keyword">open</a> <a id="224" class="Keyword">import</a> <a id="231" href="Leios.Prelude.html" class="Module">Leios.Prelude</a>
<a id="245" class="Keyword">open</a> <a id="250" class="Keyword">import</a> <a id="257" href="Leios.Abstract.html" class="Module">Leios.Abstract</a>
<a id="272" class="Keyword">open</a> <a id="277" class="Keyword">import</a> <a id="284" href="Leios.VRF.html" class="Module">Leios.VRF</a>

<a id="295" class="Keyword">module</a> <a id="302" href="Leios.Base.html" class="Module">Leios.Base</a> <a id="313" class="Symbol">(</a><a id="314" href="Leios.Base.html#314" class="Bound">a</a> <a id="316" class="Symbol">:</a> <a id="318" href="Leios.Abstract.html#452" class="Record">LeiosAbstract</a><a id="331" class="Symbol">)</a> <a id="333" class="Symbol">(</a><a id="334" class="Keyword">open</a> <a id="339" href="Leios.Abstract.html#452" class="Module">LeiosAbstract</a> <a id="353" href="Leios.Base.html#314" class="Bound">a</a><a id="354" class="Symbol">)</a> <a id="356" class="Symbol">(</a><a id="357" href="Leios.Base.html#357" class="Bound">vrf&#39;</a> <a id="362" class="Symbol">:</a> <a id="364" href="Leios.VRF.html#878" class="Record">LeiosVRF</a> <a id="373" href="Leios.Base.html#314" class="Bound">a</a><a id="374" class="Symbol">)</a>
  <a id="378" class="Symbol">(</a><a id="379" class="Keyword">let</a> <a id="383" class="Keyword">open</a> <a id="388" href="Leios.VRF.html#878" class="Module">LeiosVRF</a> <a id="397" href="Leios.Base.html#357" class="Bound">vrf&#39;</a><a id="401" class="Symbol">)</a> <a id="403" class="Keyword">where</a>

<a id="410" class="Keyword">open</a> <a id="415" class="Keyword">import</a> <a id="422" href="Leios.Blocks.html" class="Module">Leios.Blocks</a> <a id="435" href="Leios.Base.html#314" class="Bound">a</a> <a id="437" class="Keyword">using</a> <a id="443" class="Symbol">(</a><a id="444" href="Leios.Blocks.html#1236" class="Function">EndorserBlock</a><a id="457" class="Symbol">;</a> <a id="459" href="Leios.Blocks.html#1007" class="Function">EBRef</a><a id="464" class="Symbol">)</a>

<a id="StakeDistr"></a><a id="467" href="Leios.Base.html#467" class="Function">StakeDistr</a> <a id="478" class="Symbol">:</a> <a id="480" href="Agda.Primitive.html#388" class="Primitive">Type</a>
<a id="485" href="Leios.Base.html#467" class="Function">StakeDistr</a> <a id="496" class="Symbol">=</a> <a id="498" href="Axiom.Set.TotalMap.html#574" class="Record">TotalMap</a> <a id="507" href="Leios.Abstract.html#512" class="Field">PoolID</a> <a id="514" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a>

<a id="517" class="Keyword">record</a> <a id="RankingBlock"></a><a id="524" href="Leios.Base.html#524" class="Record">RankingBlock</a> <a id="537" class="Symbol">:</a> <a id="539" href="Agda.Primitive.html#388" class="Primitive">Type</a> <a id="544" class="Keyword">where</a>
  <a id="552" class="Keyword">field</a> <a id="RankingBlock.txs"></a><a id="558" href="Leios.Base.html#558" class="Field">txs</a> <a id="562" class="Symbol">:</a> <a id="564" href="Agda.Builtin.List.html#147" class="Datatype">List</a> <a id="569" href="Leios.Abstract.html#488" class="Field">Tx</a>
        <a id="RankingBlock.announcedEB"></a><a id="580" href="Leios.Base.html#580" class="Field">announcedEB</a> <a id="592" class="Symbol">:</a> <a id="594" href="Agda.Builtin.Maybe.html#135" class="Datatype">Maybe</a> <a id="600" href="Leios.Abstract.html#632" class="Field">Hash</a>
        <a id="RankingBlock.ebCert"></a><a id="613" href="Leios.Base.html#613" class="Field">ebCert</a> <a id="620" class="Symbol">:</a> <a id="622" href="Agda.Builtin.Maybe.html#135" class="Datatype">Maybe</a> <a id="628" href="Leios.Abstract.html#656" class="Field">EBCert</a>

<a id="636" class="Keyword">record</a> <a id="BaseAbstract"></a><a id="643" href="Leios.Base.html#643" class="Record">BaseAbstract</a> <a id="656" class="Symbol">:</a> <a id="658" href="Agda.Primitive.html#388" class="Primitive">Type₁</a> <a id="664" class="Keyword">where</a>
  <a id="672" class="Keyword">field</a> <a id="BaseAbstract.Cert"></a><a id="678" href="Leios.Base.html#678" class="Field">Cert</a> <a id="683" class="Symbol">:</a> <a id="685" href="Agda.Primitive.html#388" class="Primitive">Type</a>
        <a id="BaseAbstract.VTy"></a><a id="698" href="Leios.Base.html#698" class="Field">VTy</a> <a id="702" class="Symbol">:</a> <a id="704" href="Agda.Primitive.html#388" class="Primitive">Type</a>
        <a id="BaseAbstract.initSlot"></a><a id="717" href="Leios.Base.html#717" class="Field">initSlot</a> <a id="726" class="Symbol">:</a> <a id="728" href="Leios.Base.html#698" class="Field">VTy</a> <a id="732" class="Symbol">→</a> <a id="734" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a>
        <a id="BaseAbstract.V-chkCerts"></a><a id="744" href="Leios.Base.html#744" class="Field">V-chkCerts</a> <a id="755" class="Symbol">:</a> <a id="757" href="Agda.Builtin.List.html#147" class="Datatype">List</a> <a id="762" href="Leios.VRF.html#909" class="Field">PubKey</a> <a id="769" class="Symbol">→</a> <a id="771" href="Leios.Blocks.html#1236" class="Function">EndorserBlock</a> <a id="785" href="Data.Product.Base.html#1618" class="Function Operator">×</a> <a id="787" href="Leios.Base.html#678" class="Field">Cert</a> <a id="792" class="Symbol">→</a> <a id="794" href="Agda.Builtin.Bool.html#173" class="Datatype">Bool</a>
</pre>Input data type represents the possible inputs to the base layer functionality.

The base layer can receive three types of inputs:
- Initialization with a certificate validation function
- Submission of ranking blocks for processing
- Requests to fetch the current ledger state
<pre class="Agda">  <a id="1091" class="Keyword">data</a> <a id="BaseAbstract.Input"></a><a id="1096" href="Leios.Base.html#1096" class="Datatype">Input</a> <a id="1102" class="Symbol">:</a> <a id="1104" href="Agda.Primitive.html#388" class="Primitive">Type</a> <a id="1109" class="Keyword">where</a>
</pre>INIT: Initialize the base layer with a certificate validation function.

Parameters:
- (EndorserBlock × Cert → Bool): A validation function that checks
  whether an endorser block and certificate pair is valid.
  Returns True if the pair is valid, False otherwise.
<pre class="Agda">    <a id="BaseAbstract.Input.INIT"></a><a id="1396" href="Leios.Base.html#1396" class="InductiveConstructor">INIT</a>   <a id="1403" class="Symbol">:</a> <a id="1405" class="Symbol">(</a><a id="1406" href="Leios.Blocks.html#1236" class="Function">EndorserBlock</a> <a id="1420" href="Data.Product.Base.html#1618" class="Function Operator">×</a> <a id="1422" href="Leios.Base.html#678" class="Field">Cert</a> <a id="1427" class="Symbol">→</a> <a id="1429" href="Agda.Builtin.Bool.html#173" class="Datatype">Bool</a><a id="1433" class="Symbol">)</a> <a id="1435" class="Symbol">→</a> <a id="1437" href="Leios.Base.html#1096" class="Datatype">Input</a>
</pre>SUBMIT: Submit a ranking block to the base layer for processing.

Parameters:
- RankingBlock: A ranking block containing either an endorser block,
  a list of transactions, or both (using the These type constructor).
  This represents new content to be added to the ledger.
<pre class="Agda">    <a id="BaseAbstract.Input.SUBMIT"></a><a id="1733" href="Leios.Base.html#1733" class="InductiveConstructor">SUBMIT</a> <a id="1740" class="Symbol">:</a> <a id="1742" href="Leios.Base.html#524" class="Record">RankingBlock</a> <a id="1755" class="Symbol">→</a> <a id="1757" href="Leios.Base.html#1096" class="Datatype">Input</a>
</pre>FTCH-LDG: Request to fetch the current ledger state.

This input has no parameters and is used to query the current
state of the base layer ledger.
<pre class="Agda">    <a id="BaseAbstract.Input.FTCH-LDG"></a><a id="1927" href="Leios.Base.html#1927" class="InductiveConstructor">FTCH-LDG</a> <a id="1936" class="Symbol">:</a> <a id="1938" href="Leios.Base.html#1096" class="Datatype">Input</a>
</pre>Output data type represents the possible outputs from the base layer functionality.

The base layer can produce three types of outputs:
- Stake distribution information
- Empty response (no meaningful output)
- Base layer ledger contents
<pre class="Agda">  <a id="2196" class="Keyword">data</a> <a id="BaseAbstract.Output"></a><a id="2201" href="Leios.Base.html#2201" class="Datatype">Output</a> <a id="2208" class="Symbol">:</a> <a id="2210" href="Agda.Primitive.html#388" class="Primitive">Type</a> <a id="2215" class="Keyword">where</a>
</pre>STAKE: Output containing the current stake distribution.

Parameters:
- StakeDistr: A total map from pool identifiers to their stake amounts (ℕ).
  This represents how stake is distributed across different pools
  in the system.
<pre class="Agda">    <a id="BaseAbstract.Output.STAKE"></a><a id="2466" href="Leios.Base.html#2466" class="InductiveConstructor">STAKE</a> <a id="2472" class="Symbol">:</a> <a id="2474" href="Leios.Base.html#467" class="Function">StakeDistr</a> <a id="2485" class="Symbol">→</a> <a id="2487" href="Leios.Base.html#2201" class="Datatype">Output</a>
</pre>EMPTY: Empty output indicating no meaningful result.

This output is used when an operation completes successfully
but produces no data that needs to be returned to the caller.
<pre class="Agda">    <a id="BaseAbstract.Output.EMPTY"></a><a id="2687" href="Leios.Base.html#2687" class="InductiveConstructor">EMPTY</a> <a id="2693" class="Symbol">:</a> <a id="2695" href="Leios.Base.html#2201" class="Datatype">Output</a>
</pre>BASE-LDG: Output containing the base layer ledger contents.

Parameters:
- List RankingBlock: A list of ranking blocks that constitute
  the current state of the base layer ledger. Each ranking block
  may contain endorser blocks, transactions, or both.
<pre class="Agda">    <a id="BaseAbstract.Output.BASE-LDG"></a><a id="2972" href="Leios.Base.html#2972" class="InductiveConstructor">BASE-LDG</a> <a id="2981" class="Symbol">:</a> <a id="2983" href="Agda.Builtin.List.html#147" class="Datatype">List</a> <a id="2988" href="Leios.Base.html#524" class="Record">RankingBlock</a> <a id="3001" class="Symbol">→</a> <a id="3003" href="Leios.Base.html#2201" class="Datatype">Output</a>
</pre><pre class="Agda">  <a id="3024" class="Keyword">record</a> <a id="BaseAbstract.Functionality"></a><a id="3031" href="Leios.Base.html#3031" class="Record">Functionality</a> <a id="3045" class="Symbol">:</a> <a id="3047" href="Agda.Primitive.html#388" class="Primitive">Type₁</a> <a id="3053" class="Keyword">where</a>
    <a id="3063" class="Keyword">field</a> <a id="3069" href="Leios.Base.html#3069" class="Field">State</a> <a id="3075" class="Symbol">:</a> <a id="3077" href="Agda.Primitive.html#388" class="Primitive">Type</a>
          <a id="3092" href="Leios.Base.html#3092" class="Field Operator">_-⟦_/_⟧⇀_</a> <a id="3102" class="Symbol">:</a> <a id="3104" href="Leios.Base.html#3069" class="Field">State</a> <a id="3110" class="Symbol">→</a> <a id="3112" href="Leios.Base.html#1096" class="Datatype">Input</a> <a id="3118" class="Symbol">→</a> <a id="3120" href="Leios.Base.html#2201" class="Datatype">Output</a> <a id="3127" class="Symbol">→</a> <a id="3129" href="Leios.Base.html#3069" class="Field">State</a> <a id="3135" class="Symbol">→</a> <a id="3137" href="Agda.Primitive.html#388" class="Primitive">Type</a>
          <a id="3152" href="Leios.Base.html#3152" class="Field">SUBMIT-total</a> <a id="3165" class="Symbol">:</a> <a id="3167" class="Symbol">∀</a> <a id="3169" class="Symbol">{</a><a id="3170" href="Leios.Base.html#3170" class="Bound">s</a> <a id="3172" href="Leios.Base.html#3172" class="Bound">b</a><a id="3173" class="Symbol">}</a> <a id="3175" class="Symbol">→</a> <a id="3177" href="Data.Product.Base.html#1371" class="Function">∃[</a> <a id="3180" href="Leios.Base.html#3180" class="Bound">s&#39;</a> <a id="3183" href="Data.Product.Base.html#1371" class="Function">]</a> <a id="3185" href="Leios.Base.html#3170" class="Bound">s</a> <a id="3187" href="Leios.Base.html#3092" class="Field Operator">-⟦</a> <a id="3190" href="Leios.Base.html#1733" class="InductiveConstructor">SUBMIT</a> <a id="3197" href="Leios.Base.html#3172" class="Bound">b</a> <a id="3199" href="Leios.Base.html#3092" class="Field Operator">/</a> <a id="3201" href="Leios.Base.html#2687" class="InductiveConstructor">EMPTY</a> <a id="3207" href="Leios.Base.html#3092" class="Field Operator">⟧⇀</a> <a id="3210" href="Leios.Base.html#3180" class="Bound">s&#39;</a>
          <a id="3223" href="Leios.Base.html#3223" class="Field">FTCH-total</a> <a id="3234" class="Symbol">:</a> <a id="3236" class="Symbol">∀</a> <a id="3238" class="Symbol">{</a><a id="3239" href="Leios.Base.html#3239" class="Bound">s</a><a id="3240" class="Symbol">}</a> <a id="3242" class="Symbol">→</a> <a id="3244" href="Data.Product.Base.html#1371" class="Function">∃[</a> <a id="3247" href="Leios.Base.html#3247" class="Bound">r</a> <a id="3249" href="Data.Product.Base.html#1371" class="Function">]</a> <a id="3251" class="Symbol">(</a><a id="3252" href="Data.Product.Base.html#1371" class="Function">∃[</a> <a id="3255" href="Leios.Base.html#3255" class="Bound">s&#39;</a> <a id="3258" href="Data.Product.Base.html#1371" class="Function">]</a> <a id="3260" class="Symbol">(</a><a id="3261" href="Leios.Base.html#3239" class="Bound">s</a> <a id="3263" href="Leios.Base.html#3092" class="Field Operator">-⟦</a> <a id="3266" href="Leios.Base.html#1927" class="InductiveConstructor">FTCH-LDG</a> <a id="3275" href="Leios.Base.html#3092" class="Field Operator">/</a> <a id="3277" href="Leios.Base.html#2972" class="InductiveConstructor">BASE-LDG</a> <a id="3286" href="Leios.Base.html#3247" class="Bound">r</a> <a id="3288" href="Leios.Base.html#3092" class="Field Operator">⟧⇀</a> <a id="3291" href="Leios.Base.html#3255" class="Bound">s&#39;</a><a id="3293" class="Symbol">))</a>
          <a id="3306" class="Comment">-- FTCH-unique : ∀ {s s&#39; o} → s -⟦ FTCH-LDG / o ⟧⇀ s&#39; → ∃[ r ] o ≡ BASE-LDG r</a>

    <a id="3389" class="Keyword">open</a> <a id="3394" href="Leios.Base.html#1096" class="Module">Input</a> <a id="3400" class="Keyword">public</a>
    <a id="3411" class="Keyword">open</a> <a id="3416" href="Leios.Base.html#2201" class="Module">Output</a> <a id="3423" class="Keyword">public</a>
</pre>