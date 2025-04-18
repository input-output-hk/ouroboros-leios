/*
 * ATTENTION: The "eval" devtool has been used (maybe by default in mode: "development").
 * This devtool is neither made for production nor for readable output files.
 * It uses "eval()" calls to create a separate source file in the browser devtools.
 * If you are trying to read the output file, select a different devtool (https://webpack.js.org/configuration/devtool/)
 * or disable the default devtool with "devtool: false".
 * If you are looking for production-ready output files, see mode: "production" (https://webpack.js.org/configuration/mode/).
 */
var Controller;
/******/ (() => { // webpackBootstrap
/******/ 	"use strict";
/******/ 	var __webpack_modules__ = ({

/***/ "./src/controller.js":
/*!***************************!*\
  !*** ./src/controller.js ***!
  \***************************/
/***/ ((__unused_webpack_module, __webpack_exports__, __webpack_require__) => {

eval("__webpack_require__.r(__webpack_exports__);\n/* harmony export */ __webpack_require__.d(__webpack_exports__, {\n/* harmony export */   calculate: () => (/* binding */ calculate),\n/* harmony export */   discountCosts: () => (/* binding */ discountCosts),\n/* harmony export */   hyperscaleCosts: () => (/* binding */ hyperscaleCosts),\n/* harmony export */   initialize: () => (/* binding */ initialize)\n/* harmony export */ });\n\n\n\n\nconst millisecond = 0.001                 //  s/ms\nconst bit = 1 / 8                         //  B/b\nconst kilobyte = 1024                     //  B/kB\nconst gigabyte = 1024 * 1024 * 1024       //  B/GB\nconst month = 365.24 / 12 * 24 * 60 * 60  //  s/month\n\n\nfunction getFloat(ui) {\n  return parseFloat(ui.value)\n}\n\nfunction sumResources(resources) {\n  return {\n    throughput   : resources.reduce((sum, resource) => sum + resource.throughput  , 0)\n  , disk         : resources.reduce((sum, resource) => sum + resource.disk        , 0)\n  , producerVcpu : resources.reduce((sum, resource) => sum + resource.producerVcpu, 0)\n  , relayVcpu    : resources.reduce((sum, resource) => sum + resource.relayVcpu   , 0)\n  , io           : resources.reduce((sum, resource) => sum + resource.io          , 0)\n  }\n}\n\n\nfunction calculateResources(rate /*  item/slot  */, elSize, elIo, elBuild, elVerify, persistent) {\n\n  const slot = getFloat(uiSlotRate)          //  slot/s\n  const size = getFloat(elSize)              //  kB/item\n  const io = getFloat(elIo)                  //  IO/item\n  const build = getFloat(elBuild)            //  vCPU*ms/item\n  const verify = getFloat(elVerify)          //  vCPU*ms/item\n  const bps = size * rate * slot * kilobyte  //  B/s\n\n  return {\n    throughput   : bps                                                  //  B/s\n  , disk         : persistent ? bps : 0                                 //  B/s\n  , producerVcpu : Math.max(build, verify) * rate * slot * millisecond  //  vCPU\n  , relayVcpu    : verify * rate * slot * millisecond                   //  vCPU\n  , io           : io * rate * slot                                     //  IO/s\n  }\n\n}\n\nfunction ibResources() {\n  const rate = getFloat(uiIbRate)  //  IB/slot\n  return calculateResources(rate, uiIbSize, uiIbIo, uiIbBuild, uiIbVerify, true)\n}\n\nfunction ebResources() {\n  const ebRate = getFloat(uiEbRate)      //  EB/pipline\n  const pipeline = getFloat(uiPhase)     //  slot/pipeline\n  const rate = ebRate / pipeline         //  EB/slot\n  return calculateResources(rate, uiEbSize, uiEbIo, uiEbBuild, uiEbVerify, true)\n}\n\nfunction voteResources() {\n  const voteRate = getFloat(uiVoteRate)  //  vote/pipline\n  const pipeline = getFloat(uiPhase)     //  slot/pipeline\n  const rate = voteRate / pipeline       //  vote/slot\n  return calculateResources(rate, uiVoteSize, uiVoteIo, uiVoteBuild, uiVoteVerify, false)\n}\n\nfunction certResources() {\n  const certRate = getFloat(uiCertRate)  //  cert/pipline\n  const pipeline = getFloat(uiPhase)     //  slot/pipeline\n  const rate = certRate / pipeline       //  cert/slot\n  return calculateResources(rate, uiCertSize, uiCertIo, uiCertBuild, uiCertVerify, false)\n}\n\nfunction rbResources() {\n  const rate = getFloat(uiRbRate)  //  RB/slot\n  return calculateResources(rate, uiRbSize, uiRbIo, uiRbBuild, uiRbVerify, true)\n}\n\nfunction txResources() {\n\n  const rate = getFloat(uiPraosTx) + getFloat(uiLeiosTx)  //  tx/s\n  const size = getFloat(uiTxSize)                         //  kB/tx\n  const verify = getFloat(uiTxVerify)                     //  vCPU*ms/tx\n  const vcpu = rate * verify * millisecond                //  vCPU\n  const mempool = rate * size * kilobyte                  //  B/s\n\n  return {\n    throughput   : mempool\n  , disk         : 0\n  , producerVcpu : vcpu\n  , relayVcpu    : vcpu\n  , io           : 0\n  }\n\n}\n\n\nasync function calculate() {\n\n  // The variable names and units are awkard here: Because of Leios\n  // parallelism, the number of slots per pipeline equals the number\n  // of phases per pipeline.\n\n  const slot = getFloat(uiSlotRate)   //  slot/s\n  const phases = getFloat(uiPhases)   //  phase/pipeline\n  const pipeline = getFloat(uiPhase)  //  slot/pipeline\n\n  const ibRate = getFloat(uiIbRate)      //  IB/slot\n  const ebRate = getFloat(uiEbRate)      //  EB/pipeline\n  const certRate = getFloat(uiCertRate)  //  cert/pipeline\n  const rbRate = getFloat(uiRbRate)      //  RB/slot\n\n  const praosTxRate = getFloat(uiPraosTx)  //  tx/s\n  const leiosTxRate = getFloat(uiLeiosTx)  //  tx/s\n\n  const txSize = getFloat(uiTxSize)      //  kB/tx\n  const ibRefSize = getFloat(uiIbRef)    //  kB/IBref\n  const certSize = getFloat(uiCertSize)  //  kB/cert\n\n  uiRbSize.value = ((praosTxRate * txSize / slot + certRate * certSize / pipeline) / rbRate).toFixed(2)       //  kB/RB\n  uiIbSize.value = (leiosTxRate == 0 && ibRate == 0 ? 0 : leiosTxRate * txSize / ibRate / slot).toFixed(2)    //  kB/IB\n  uiEbSize.value = (leiosTxRate == 0 && ibRate == 0 ? 0 : ibRate * pipeline / ebRate * ibRefSize).toFixed(2)  //  kB/EB\n\n  const resources = sumResources([\n    ibResources()\n  , ebResources()\n  , voteResources()\n  , certResources()\n  , rbResources()\n  , txResources()\n  ])\n\n  const spike = getFloat(uiSpike)\n  const producers = getFloat(uiProducers)\n  const relays = getFloat(uiRelays)\n  const nodes = producers + relays\n\n  const vcpu = producers * Math.max(2, Math.ceil(spike * resources.producerVcpu))\n             + relays    * Math.max(2, Math.ceil(spike * resources.relayVcpu   ))\n  uiTotalVcpu.innerText = vcpu\n  const costVcpu = vcpu * getFloat(uiVcpu)\n  uiCostVcpu.innerText = costVcpu.toFixed(2)\n\n  uiAmortized.style.textDecoration = uiAmortize.checked ? \"none\" : \"line-through\"\n  const discount = getFloat(uiDiscount) / 100 / 12                                                  //  1/month\n  const perpetual = uiAmortize.checked ? (1 + discount) / discount : 1                              //  1\n  const compression = 1 - getFloat(uiCompression) / 100                                             //  1\n  const storage = nodes * compression * (getFloat(uiRbLedger) + resources.disk / gigabyte * month)  //  GB/month\n  uiTotalStorage.innerText = storage.toFixed(2)\n  const costStorage = storage * perpetual * getFloat(uiStorage)\n  uiCostStorage.innerText = costStorage.toFixed(2)\n\n  const throughput = resources.throughput                     //  B/s\n  const downstream = getFloat(uiDownsteam) * throughput       //  B/s\n  const upstream = getFloat(uiUpstream) * throughput          //  B/S\n  const network = (downstream + upstream) / gigabyte * month  //  GB/month\n  uiTotalEgress.innerText = network.toFixed(2)\n  const costEgress = network * getFloat(uiEgress)\n  uiCostEgress.innerText = costEgress.toFixed(2)\n\n  uiNic.innerText = Math.max(1, Math.round(Math.pow(10, Math.ceil(Math.log(spike * Math.max(upstream, downstream) / gigabyte / bit) / Math.log(10)))))  // Gb/s\n\n  const io = spike * nodes * resources.io  // IO/s\n  uiTotalIops.innerText = io.toFixed(2)\n  const costIops = io * getFloat(uiIops)\n  uiCostIops.innerText = costIops.toFixed(2)\n\n  const cost = costVcpu + costStorage + costIops + costEgress\n  uiCost.innerText = cost.toFixed(2)\n\n  const txRate = praosTxRate + leiosTxRate                               //  tx/s\n  const txFee = getFloat(uiTxFee) * getFloat(uiTxSize)                   //  ADA/tx\n  const price = getFloat(uiAda)                                          //  USD/ADA\n  const totalFees = txRate * txFee * price * month                       //  USD/month\n  const fraction = getFloat(uiStake) / 100 * getFloat(uiRetained) / 100  //  %/100\n  const retained = fraction * totalFees                                  //  USD/month\n\n  uiFees.innerText = retained.toFixed(2)\n  uiProfit.innerText = (retained - cost).toFixed(2)\n  uiReturn.innerText = (100 * retained / cost).toFixed(2)\n\n  const txCostUSD = cost / fraction / txRate / month  //  USD/tx\n  const txCostADA = txCostUSD / price                 //  ADA/tx\n  uiCostTxUsd.innerText = txCostUSD.toFixed(2)\n  uiCostTxAda.innerText = txCostADA.toFixed(2)\n  \n}\n\nasync function hyperscaleCosts() {\n  uiVcpu.value = \"20\"\n  uiStorage.value = \"0.12\"\n  uiIops.value = \"0.05\"\n  uiEgress.value = \"0.09\"\n  calculate()\n}\n\nasync function discountCosts() {\n  uiVcpu.value = \"20\"\n  uiStorage.value = \"0.10\"\n  uiIops.value = \"0.00\"\n  uiEgress.value = \"0.00\"\n  calculate()\n}\n\nasync function initialize() {\n  [\n    uiAda\n  , uiAmortize\n  , uiCertBuild\n  , uiCertIo\n  , uiCertRate\n  , uiCertSize\n  , uiCertVerify\n  , uiCompression\n  , uiDiscount\n  , uiDownsteam\n  , uiEbBuild\n  , uiEbIo\n  , uiEbRate\n//, uiEbSize\n  , uiEbVerify\n  , uiEgress\n  , uiIbBuild\n  , uiIbIo\n  , uiIbRate\n  , uiIbRef\n//, uiIbSize\n  , uiIbVerify\n  , uiIops\n  , uiLeiosTx\n  , uiPhase\n//, uiPhases\n  , uiPraosTx\n  , uiProducers\n  , uiRbBuild\n  , uiRbLedger\n  , uiRbRate\n//, uiRbSize\n  , uiRbIo\n  , uiRbVerify\n  , uiRelays\n  , uiRetained\n  , uiSlotRate\n  , uiSpike\n  , uiStake\n  , uiStorage\n  , uiTxFee\n  , uiTxSize\n  , uiTxVerify\n  , uiUpstream\n//, uiVariant\n  , uiVcpu\n  , uiVoteBuild\n  , uiVoteIo\n  , uiVoteRate\n  , uiVoteSize\n  , uiVoteVerify\n  ].forEach(el => el.addEventListener(\"input\", calculate))\n\n  calculate()\n}\n\n\n//# sourceURL=webpack://Controller/./src/controller.js?");

/***/ })

/******/ 	});
/************************************************************************/
/******/ 	// The require scope
/******/ 	var __webpack_require__ = {};
/******/ 	
/************************************************************************/
/******/ 	/* webpack/runtime/define property getters */
/******/ 	(() => {
/******/ 		// define getter functions for harmony exports
/******/ 		__webpack_require__.d = (exports, definition) => {
/******/ 			for(var key in definition) {
/******/ 				if(__webpack_require__.o(definition, key) && !__webpack_require__.o(exports, key)) {
/******/ 					Object.defineProperty(exports, key, { enumerable: true, get: definition[key] });
/******/ 				}
/******/ 			}
/******/ 		};
/******/ 	})();
/******/ 	
/******/ 	/* webpack/runtime/hasOwnProperty shorthand */
/******/ 	(() => {
/******/ 		__webpack_require__.o = (obj, prop) => (Object.prototype.hasOwnProperty.call(obj, prop))
/******/ 	})();
/******/ 	
/******/ 	/* webpack/runtime/make namespace object */
/******/ 	(() => {
/******/ 		// define __esModule on exports
/******/ 		__webpack_require__.r = (exports) => {
/******/ 			if(typeof Symbol !== 'undefined' && Symbol.toStringTag) {
/******/ 				Object.defineProperty(exports, Symbol.toStringTag, { value: 'Module' });
/******/ 			}
/******/ 			Object.defineProperty(exports, '__esModule', { value: true });
/******/ 		};
/******/ 	})();
/******/ 	
/************************************************************************/
/******/ 	
/******/ 	// startup
/******/ 	// Load entry module and return exports
/******/ 	// This entry module can't be inlined because the eval devtool is used.
/******/ 	var __webpack_exports__ = {};
/******/ 	__webpack_modules__["./src/controller.js"](0, __webpack_exports__, __webpack_require__);
/******/ 	Controller = __webpack_exports__;
/******/ 	
/******/ })()
;