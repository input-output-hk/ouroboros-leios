This module serves as the main entry point for the Leios formal specification.
It imports all the core modules that together define the complete Leios protocol.
<!--
<pre class="Agda"><a id="175" class="Symbol">{-#</a> <a id="179" class="Keyword">OPTIONS</a> <a id="187" class="Pragma">--safe</a> <a id="194" class="Symbol">#-}</a>
</pre>-->
<pre class="Agda"><a id="214" class="Keyword">module</a> <a id="221" href="formal-spec.html" class="Module">formal-spec</a> <a id="233" class="Keyword">where</a>
</pre>### Prelude
TODO: move into iog-agda-prelude
<pre class="Agda"><a id="296" class="Keyword">open</a> <a id="301" class="Keyword">import</a> <a id="308" href="Prelude.Result.html" class="Module">Prelude.Result</a>
<a id="323" class="Keyword">open</a> <a id="328" class="Keyword">import</a> <a id="335" href="Prelude.Errors.html" class="Module">Prelude.Errors</a>
</pre>### Core Protocol Components
Abstract interface, specifying core types and functions
<pre class="Agda"><a id="447" class="Keyword">open</a> <a id="452" class="Keyword">import</a> <a id="459" href="Leios.Abstract.html" class="Module">Leios.Abstract</a>
</pre>Fundamental types and structures
<pre class="Agda"><a id="519" class="Keyword">open</a> <a id="524" class="Keyword">import</a> <a id="531" href="Leios.Base.html" class="Module">Leios.Base</a>
</pre>Block structure and validation
<pre class="Agda"><a id="585" class="Keyword">open</a> <a id="590" class="Keyword">import</a> <a id="597" href="Leios.Blocks.html" class="Module">Leios.Blocks</a>
</pre>Protocol parameters and configuration
<pre class="Agda"><a id="660" class="Keyword">open</a> <a id="665" class="Keyword">import</a> <a id="672" href="Leios.Config.html" class="Module">Leios.Config</a>
</pre>Freshest first delivery abstraction
<pre class="Agda"><a id="733" class="Keyword">open</a> <a id="738" class="Keyword">import</a> <a id="745" href="Leios.FFD.html" class="Module">Leios.FFD</a>
</pre>Key registration abstraction
<pre class="Agda"><a id="796" class="Keyword">open</a> <a id="801" class="Keyword">import</a> <a id="808" href="Leios.KeyRegistration.html" class="Module">Leios.KeyRegistration</a>
</pre>Project specific prelude
<pre class="Agda"><a id="867" class="Keyword">open</a> <a id="872" class="Keyword">import</a> <a id="879" href="Leios.Prelude.html" class="Module">Leios.Prelude</a>
</pre>Main protocol definition
<pre class="Agda"><a id="930" class="Keyword">open</a> <a id="935" class="Keyword">import</a> <a id="942" href="Leios.Protocol.html" class="Module">Leios.Protocol</a>
</pre>Abstractions bundled
<pre class="Agda"><a id="990" class="Keyword">open</a> <a id="995" class="Keyword">import</a> <a id="1002" href="Leios.SpecStructure.html" class="Module">Leios.SpecStructure</a>
</pre>Voting mechanism specification
<pre class="Agda"><a id="1065" class="Keyword">import</a> <a id="1072" href="Leios.Voting.Channel.html" class="Module">Leios.Voting.Channel</a>
<a id="1093" class="Keyword">import</a> <a id="1100" href="Leios.Voting.Ideal.html" class="Module">Leios.Voting.Ideal</a>
<a id="1119" class="Keyword">import</a> <a id="1126" href="Leios.Voting.Certifier.html" class="Module">Leios.Voting.Certifier</a>
<a id="1149" class="Keyword">import</a> <a id="1156" href="Leios.Voting.Real.html" class="Module">Leios.Voting.Real</a>
<a id="1174" class="Keyword">import</a> <a id="1181" href="Leios.Voting.Voter.html" class="Module">Leios.Voting.Voter</a>
</pre>Verifiable Random Function implementation
<pre class="Agda"><a id="1254" class="Keyword">open</a> <a id="1259" class="Keyword">import</a> <a id="1266" href="Leios.VRF.html" class="Module">Leios.VRF</a>
</pre>Linear Leios specification
<pre class="Agda"><a id="1315" class="Keyword">open</a> <a id="1320" class="Keyword">import</a> <a id="1327" href="Leios.Linear.html" class="Module">Leios.Linear</a>
</pre>Progress of the Linear Leios node: enough traces exist for the invariants to
say something
<pre class="Agda"><a id="1443" class="Keyword">import</a> <a id="1450" href="Leios.Linear.Progress.html" class="Module">Leios.Linear.Progress</a>
</pre>### Cryptographic Foundations
Category-theoretic approach to cryptography
<pre class="Agda"><a id="1558" class="Keyword">open</a> <a id="1563" class="Keyword">import</a> <a id="1570" href="CategoricalCrypto.html" class="Module">CategoricalCrypto</a>
<a id="1588" class="Keyword">import</a> <a id="1595" href="CategoricalCrypto.Ext.html" class="Module">CategoricalCrypto.Ext</a>
</pre>### Blockchain abstractions
<pre class="Agda"><a id="1657" class="Keyword">import</a> <a id="1664" href="Blockchain.Liveness.Transfer.html" class="Module">Blockchain.Liveness.Transfer</a>
</pre>### Network Layer
Basic broadcast networking primitives
<pre class="Agda"><a id="1761" class="Keyword">open</a> <a id="1766" class="Keyword">import</a> <a id="1773" href="Network.BasicBroadcast.html" class="Module">Network.BasicBroadcast</a>
</pre>The Leios deployment over the diffusion network, and the transfer of safety
and liveness from the base chain
<pre class="Agda"><a id="1917" class="Keyword">open</a> <a id="1922" class="Keyword">import</a> <a id="1929" href="Network.Leios.html" class="Module">Network.Leios</a>
</pre>### Verification and Testing
Trace verification for protocol properties
<pre class="Agda"><a id="2027" class="Keyword">open</a> <a id="2032" class="Keyword">import</a> <a id="2039" href="Leios.Linear.Trace.Verifier.html" class="Module">Leios.Linear.Trace.Verifier</a>
<a id="2067" class="Keyword">open</a> <a id="2072" class="Keyword">import</a> <a id="2079" href="Leios.Linear.Trace.Verifier.Test.html" class="Module">Leios.Linear.Trace.Verifier.Test</a>
<a id="2112" class="Keyword">open</a> <a id="2117" class="Keyword">import</a> <a id="2124" href="Test.Defaults.html" class="Module">Test.Defaults</a>
</pre>