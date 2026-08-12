## Leios.Config

This module defines the configuration parameters for the Leios protocol.
It includes block type definitions (Input Blocks, Endorser Blocks, Votes)
and protocol parameters such as party counts, stake distribution,
stage length, and winning slot specifications.
<!--
<pre class="Agda"><a id="291" class="Symbol">{-#</a> <a id="295" class="Keyword">OPTIONS</a> <a id="303" class="Pragma">--safe</a> <a id="310" class="Symbol">#-}</a>
</pre>-->
<pre class="Agda"><a id="330" class="Keyword">open</a> <a id="335" class="Keyword">import</a> <a id="342" href="Leios.Prelude.html" class="Module">Leios.Prelude</a>
<a id="356" class="Keyword">open</a> <a id="361" class="Keyword">import</a> <a id="368" href="Tactic.Defaults.html" class="Module">Tactic.Defaults</a>
<a id="384" class="Keyword">open</a> <a id="389" class="Keyword">import</a> <a id="396" href="Tactic.Derive.DecEq.html" class="Module">Tactic.Derive.DecEq</a>

<a id="417" class="Keyword">module</a> <a id="424" href="Leios.Config.html" class="Module">Leios.Config</a> <a id="437" class="Keyword">where</a>

<a id="444" class="Keyword">data</a> <a id="BlockType"></a><a id="449" href="Leios.Config.html#449" class="Datatype">BlockType</a> <a id="459" class="Symbol">:</a> <a id="461" href="Agda.Primitive.html#388" class="Primitive">Type</a> <a id="466" class="Keyword">where</a>
  <a id="BlockType.IB"></a><a id="474" href="Leios.Config.html#474" class="InductiveConstructor">IB</a> <a id="BlockType.EB"></a><a id="477" href="Leios.Config.html#477" class="InductiveConstructor">EB</a> <a id="BlockType.VT"></a><a id="480" href="Leios.Config.html#480" class="InductiveConstructor">VT</a> <a id="483" class="Symbol">:</a> <a id="485" href="Leios.Config.html#449" class="Datatype">BlockType</a>

<a id="496" class="Keyword">unquoteDecl</a> <a id="DecEq-BlockType"></a><a id="508" href="Leios.Config.html#508" class="Function">DecEq-BlockType</a> <a id="524" class="Symbol">=</a> <a id="526" href="Tactic.Derive.DecEq.html#5150" class="Function">derive-DecEq</a> <a id="539" class="Symbol">((</a><a id="541" class="Keyword">quote</a> <a id="547" href="Leios.Config.html#449" class="Datatype">BlockType</a> <a id="557" href="Agda.Builtin.Sigma.html#235" class="InductiveConstructor Operator">,</a> <a id="559" href="Leios.Config.html#508" class="Function">DecEq-BlockType</a><a id="574" class="Symbol">)</a> <a id="576" href="Agda.Builtin.List.html#199" class="InductiveConstructor Operator">∷</a> <a id="578" href="Agda.Builtin.List.html#184" class="InductiveConstructor">[]</a><a id="580" class="Symbol">)</a>

<a id="583" class="Keyword">record</a> <a id="NetworkParams"></a><a id="590" href="Leios.Config.html#590" class="Record">NetworkParams</a> <a id="604" class="Symbol">:</a> <a id="606" href="Agda.Primitive.html#388" class="Primitive">Type</a> <a id="611" class="Keyword">where</a>
  <a id="619" class="Keyword">field</a> <a id="NetworkParams.numberOfParties"></a><a id="625" href="Leios.Config.html#625" class="Field">numberOfParties</a>   <a id="643" class="Symbol">:</a> <a id="645" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a>
        <a id="NetworkParams.stakeDistribution"></a><a id="655" href="Leios.Config.html#655" class="Field">stakeDistribution</a> <a id="673" class="Symbol">:</a> <a id="675" href="Axiom.Set.TotalMap.html#574" class="Record">TotalMap</a> <a id="684" class="Symbol">(</a><a id="685" href="Data.Fin.Base.html#1132" class="Datatype">Fin</a> <a id="689" href="Leios.Config.html#625" class="Field">numberOfParties</a><a id="704" class="Symbol">)</a> <a id="706" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a>
        <a id="716" class="Symbol">⦃</a> <a id="NetworkParams.NonZero-numberOfParties"></a><a id="718" href="Leios.Config.html#718" class="Field">NonZero-numberOfParties</a> <a id="742" class="Symbol">⦄</a> <a id="744" class="Symbol">:</a> <a id="746" href="Data.Nat.Base.html#3266" class="Record">NonZero</a> <a id="754" href="Leios.Config.html#625" class="Field">numberOfParties</a>

<a id="771" class="Keyword">record</a> <a id="Params"></a><a id="778" href="Leios.Config.html#778" class="Record">Params</a> <a id="785" class="Symbol">:</a> <a id="787" href="Agda.Primitive.html#388" class="Primitive">Type</a> <a id="792" class="Keyword">where</a>
  <a id="800" class="Keyword">field</a> <a id="Params.networkParams"></a><a id="806" href="Leios.Config.html#806" class="Field">networkParams</a>    <a id="823" class="Symbol">:</a> <a id="825" href="Leios.Config.html#590" class="Record">NetworkParams</a>
        <a id="Params.Lhdr"></a><a id="847" href="Leios.Config.html#847" class="Field">Lhdr</a> <a id="Params.Lvote"></a><a id="852" href="Leios.Config.html#852" class="Field">Lvote</a> <a id="Params.Ldiff"></a><a id="858" href="Leios.Config.html#858" class="Field">Ldiff</a> <a id="864" class="Symbol">:</a> <a id="866" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a>
        <a id="876" class="Comment">-- CIP-0164 committee stake coverage σc, as a ratio σc-num / σc-den</a>
        <a id="952" class="Comment">-- (e.g. 99 / 100): the voting committee is the stake-descending</a>
        <a id="1025" class="Comment">-- prefix of pools whose cumulative stake reaches σc of the total.</a>
        <a id="Params.σc-num"></a><a id="1100" href="Leios.Config.html#1100" class="Field">σc-num</a> <a id="Params.σc-den"></a><a id="1107" href="Leios.Config.html#1107" class="Field">σc-den</a>    <a id="1117" class="Symbol">:</a> <a id="1119" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a>

  <a id="1124" class="Keyword">open</a> <a id="1129" href="Leios.Config.html#590" class="Module">NetworkParams</a> <a id="1143" href="Leios.Config.html#806" class="Field">networkParams</a> <a id="1157" class="Keyword">public</a>

<a id="1165" class="Keyword">module</a> <a id="1172" href="Leios.Config.html#1172" class="Module">_</a> <a id="1174" class="Symbol">(</a><a id="1175" href="Leios.Config.html#1175" class="Bound">params</a> <a id="1182" class="Symbol">:</a> <a id="1184" href="Leios.Config.html#778" class="Record">Params</a><a id="1190" class="Symbol">)</a> <a id="1192" class="Keyword">where</a>
  <a id="1200" class="Keyword">open</a> <a id="1205" href="Leios.Config.html#778" class="Module">Params</a> <a id="1212" href="Leios.Config.html#1175" class="Bound">params</a>

  <a id="1222" class="Keyword">private</a>
    <a id="1234" href="Leios.Config.html#1234" class="Function">allStakes</a> <a id="1244" class="Symbol">:</a> <a id="1246" href="Agda.Builtin.List.html#147" class="Datatype">List</a> <a id="1251" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a>
    <a id="1257" href="Leios.Config.html#1234" class="Function">allStakes</a> <a id="1267" class="Symbol">=</a> <a id="1269" href="Data.List.Base.html#6139" class="Function">L.tabulate</a> <a id="1280" class="Symbol">(</a><a id="1281" href="Axiom.Set.TotalMap.html#779" class="Function">TotalMap.lookup</a> <a id="1297" href="Leios.Config.html#655" class="Function">stakeDistribution</a><a id="1314" class="Symbol">)</a>

    <a id="1321" href="Leios.Config.html#1321" class="Function">totalStake</a> <a id="1332" class="Symbol">:</a> <a id="1334" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a>
    <a id="1340" href="Leios.Config.html#1321" class="Function">totalStake</a> <a id="1351" class="Symbol">=</a> <a id="1353" href="Data.List.Base.html#17278" class="Function">L.sum</a> <a id="1359" href="Leios.Config.html#1234" class="Function">allStakes</a>

    <a id="1374" class="Comment">-- stake held by pools with strictly more stake than the given one</a>
    <a id="1445" href="Leios.Config.html#1445" class="Function">richerStake</a> <a id="1457" class="Symbol">:</a> <a id="1459" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a> <a id="1461" class="Symbol">→</a> <a id="1463" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a>
    <a id="1469" href="Leios.Config.html#1445" class="Function">richerStake</a> <a id="1481" href="Leios.Config.html#1481" class="Bound">st</a> <a id="1484" class="Symbol">=</a> <a id="1486" href="Data.List.Base.html#17278" class="Function">L.sum</a> <a id="1492" class="Symbol">(</a><a id="1493" href="Data.List.Base.html#10389" class="Function">L.filter</a> <a id="1502" class="Symbol">(</a><a id="1503" href="Leios.Config.html#1481" class="Bound">st</a> <a id="1506" href="Class.HasOrder.Core.html#1076" class="Function Operator">&lt;?_</a><a id="1509" class="Symbol">)</a> <a id="1511" href="Leios.Config.html#1234" class="Function">allStakes</a><a id="1520" class="Symbol">)</a>

  <a id="1525" class="Comment">-- Voting-committee membership by stake-based truncation (CIP-0164,</a>
  <a id="1595" class="Comment">-- &quot;Committee Structure&quot;): order pools by stake descending and accumulate</a>
  <a id="1671" class="Comment">-- until the cumulative stake covers the σc target; the committee is fixed</a>
  <a id="1748" class="Comment">-- for the whole epoch. A pool with stake `st` is on the committee iff the</a>
  <a id="1825" class="Comment">-- pools with strictly more stake do not already cover the target. Pools of</a>
  <a id="1903" class="Comment">-- equal stake at the boundary are all included (the CIP fixes no tie</a>
  <a id="1975" class="Comment">-- order).</a>
  <a id="1988" href="Leios.Config.html#1988" class="Function">inVotingCommittee</a> <a id="2006" class="Symbol">:</a> <a id="2008" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a> <a id="2010" class="Symbol">→</a> <a id="2012" href="Agda.Primitive.html#388" class="Primitive">Type</a>
  <a id="2019" href="Leios.Config.html#1988" class="Function">inVotingCommittee</a> <a id="2037" href="Leios.Config.html#2037" class="Bound">st</a> <a id="2040" class="Symbol">=</a> <a id="2042" href="Leios.Config.html#1445" class="Function">richerStake</a> <a id="2054" href="Leios.Config.html#2037" class="Bound">st</a> <a id="2057" href="Agda.Builtin.Nat.html#539" class="Primitive Operator">*</a> <a id="2059" href="Leios.Config.html#1107" class="Field">σc-den</a> <a id="2066" href="Class.HasOrder.Core.html#646" class="Field Operator">&lt;</a> <a id="2068" href="Leios.Config.html#1321" class="Function">totalStake</a> <a id="2079" href="Agda.Builtin.Nat.html#539" class="Primitive Operator">*</a> <a id="2081" href="Leios.Config.html#1100" class="Field">σc-num</a>

<a id="2089" class="Keyword">record</a> <a id="TestParams"></a><a id="2096" href="Leios.Config.html#2096" class="Record">TestParams</a> <a id="2107" class="Symbol">(</a><a id="2108" href="Leios.Config.html#2108" class="Bound">params</a> <a id="2115" class="Symbol">:</a> <a id="2117" href="Leios.Config.html#778" class="Record">Params</a><a id="2123" class="Symbol">)</a> <a id="2125" class="Symbol">:</a> <a id="2127" href="Agda.Primitive.html#388" class="Primitive">Type</a> <a id="2132" class="Keyword">where</a>
  <a id="2140" class="Keyword">open</a> <a id="2145" href="Leios.Config.html#778" class="Module">Params</a> <a id="2152" href="Leios.Config.html#2108" class="Bound">params</a>

  <a id="2162" class="Keyword">field</a> <a id="TestParams.sutId"></a><a id="2168" href="Leios.Config.html#2168" class="Field">sutId</a> <a id="2174" class="Symbol">:</a> <a id="2176" href="Data.Fin.Base.html#1132" class="Datatype">Fin</a> <a id="2180" href="Leios.Config.html#625" class="Function">numberOfParties</a>
        <a id="TestParams.winning-slots"></a><a id="2204" href="Leios.Config.html#2204" class="Field">winning-slots</a> <a id="2218" class="Symbol">:</a> <a id="2220" href="abstract-set-theory.FiniteSetTheory.html#488" class="Function Operator">ℙ</a> <a id="2222" class="Symbol">(</a><a id="2223" href="Leios.Config.html#449" class="Datatype">BlockType</a> <a id="2233" href="Data.Product.Base.html#1618" class="Function Operator">×</a> <a id="2235" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a><a id="2236" class="Symbol">)</a>
</pre>