var sessionId; // This value will be defined by the first message sent by the server via the websocket.

var parameters = {};

document.addEventListener('DOMContentLoaded', () => {


  function sliceOf(slot) {
    return Math.floor(slot / parameters._L);
  }

  const node = document.getElementById('main_chart');

  // throughput chart
  const chart = new Chart(node, {
    title: {
      text: "Leios Blocks throughput"
    },
    data: {
      // N.B.: Make sure colors are picked from an inclusive color palette.
      // See for instance: https://medium.com/@allieofisher/inclusive-color-palettes-for-the-web-bbfe8cf2410e
      datasets: [
        {
          type: 'scatter',
          label: "Created IBs",
          data: [],
          backgroundColor: '#6FDE6E',
          borderColor: '#6FDE6E',
        },
        {
          type: 'scatter',
          label: "Linked IBs",
          data: [],
          backgroundColor: '#235FA4',
          borderColor: '#235FA4',
        },
        {
          type: 'scatter',
          label: "Dropped IBs",
          data: [],
          backgroundColor: '#FF4242',
          borderColor: '#FF4242',
        }
      ]
    },
    options: {
      scales: {
        x: {
          type: 'linear',
          title: {
            text: 'Slots',
            display: true
          },
          min: 0,
          max: 50
        }
      }
    }
  });

  // retrieve simulation data from server
  const wsPath = window.location.pathname.split('/').slice(0, -1).join('/');
  const protocol = (window.location.protocol === 'https:') ? 'wss:' : 'ws:';
  const ws = new WebSocket(`${protocol}//${window.location.hostname}:${window.location.port}${wsPath}`);

  ws.onopen = function() {
    console.log('connected');
  };

  // We will add elements to the queue when we get a log message about
  // a new IB being created. When we receive a log message about a
  // created EB, we will remove the linked IBs inside the EB from the
  // queue.
  var queuedIBs = [];

  // accumulate the size of all endorsed IBs.
  var total_endorsed_data = 0;
  var total_dropped_data = 0;
  var total_endorsed_IBs = 0;
  var total_endorsed_latency = 0;

  var currentSlot = 0;

  // Trim the chart data to the last 50 entries.
  function adjust(chart) {
    const minx = chart.data.datasets[0].data[0].x;
    chart.options.scales.x.min = minx;
    chart.options.scales.x.max = minx + 50;
  }

  function adjustRates() {
    const throughput = document.getElementById('throughput');
    throughput.value = (total_endorsed_data / (currentSlot + 1)).toFixed(2);

    const dropped_rate = document.getElementById('dropped_rate');
    dropped_rate.value = (total_dropped_data / (currentSlot + 1)).toFixed(2);

    const latency = document.getElementById('latency');
    latency.value = (total_endorsed_latency / (total_endorsed_IBs + 1)).toFixed(2);
  }

  ws.onmessage = function(message) {
    if (message.data) {
      const logData = JSON.parse(message.data);

      // Keep only the last 50 entries
      //
      // TODO: find out why the chart won't display properly if this is done after pushing data.
      if (chart.data.datasets[0].data.length > 49) {
        chart.data.datasets[0].data.splice(0, chart.data.datasets[0].data.length - 49);
      }

      switch (logData.tag) {
        case 'NextSlot': {
          currentSlot = logData.slot;
          adjustRates();
          break;
        }
        case 'SessionId': {
          sessionId = logData.sessionId;
          console.log(`Got session id ${sessionId}`);

          // Set the parameters in the UI using the server default parameters.
          getJSON(`/api/parameters?sessionId=${sessionId}`)
            .then((data) => {
              document.getElementById('input_L').value = data._L;
              document.getElementById('input_lambda').value = data.λ;
              document.getElementById('input_f_I').value = data.f_I;
              document.getElementById('input_f_E').value = data.f_E;
              document.getElementById('input_node_bandwidth').value = data.nodeBandwidth;
              document.getElementById('input_ib_size').value = data.ibSize;
            });
          break;
        }
        case 'ReceivedEB': {

          if (logData.receivedEB.eb_linked_IBs.length != 0) {
            queuedIBs = _.differenceWith(queuedIBs, logData.receivedEB.eb_linked_IBs, _.isEqual);
            total_endorsed_data += logData.receivedEB.eb_linked_IBs.map(ib => ib.ib_size).reduce((a, b) => a + b, 0);
            total_endorsed_IBs += logData.receivedEB.eb_linked_IBs.length;
            total_endorsed_latency += logData.receivedEB.eb_linked_IBs.map(ib => logData.receivedEB.eb_slot - ib.ib_slot).reduce((a, b) => a + b, 0);
          }

          // We know that future EBs will link IBs whose slots are
          // greater or equal than the slice linked by the current
          // EB. Therefore we can regard all those IBs with smaller
          // slots as *lost*.
          const droppedIBs = queuedIBs.filter(ib =>
            sliceOf(ib.ib_slot) < sliceOf(logData.receivedEB.eb_slot) - (parameters.λ + 1)
          );

          queuedIBs = _.differenceWith(queuedIBs, droppedIBs, _.isEqual);

          var i = chart.data.datasets[1].data.findIndex(p => p.x == logData.receivedEB.eb_slot);
          if (0 <= i) {
            chart.data.datasets[1].data[i] = {
              x: logData.receivedEB.eb_slot,
              y: chart.data.datasets[1].data[i].y + logData.receivedEB.eb_linked_IBs.length
            };
          } else {
            chart.data.datasets[1].data.push({
              x: logData.receivedEB.eb_slot,
              y: logData.receivedEB.eb_linked_IBs.length
            });
          }

          if (droppedIBs.length > 0) {
            total_dropped_data += droppedIBs.map(ib => ib.ib_size).reduce((a, b) => a + b, 0);
            chart.data.datasets[2].data.push({
              x: logData.receivedEB.eb_slot,
              y: droppedIBs.length
            });
          }

          adjust(chart);
          chart.update();

          break;
        }
        case 'ProducedIB': {
          queuedIBs.push(logData.producedIB);

          var i = chart.data.datasets[0].data.findIndex(p => p.x == logData.producedIB.ib_slot);
          if (0 <= i) {
            chart.data.datasets[0].data[i] = {
              x: logData.producedIB.ib_slot,
              y: chart.data.datasets[0].data[i].y + 1
            };
          } else {
            chart.data.datasets[0].data.push({
              x: logData.producedIB.ib_slot,
              y: 1
            });
          }

          adjust(chart);
          chart.update();

          break;
        }
      }

    };
  };

  window.onbeforeunload = _ => {
    ws.close();
  };

  ws.onclose = function() {
    console.log('disconnected');
  };

  /*
   * Parameters change handling
   */
  onParametersChange('input_L',
    (newValue) => { parameters._L = newValue },
    `/api/set-L`);

  onParametersChange('input_lambda',
    (newValue) => { parameters.λ = newValue },
    `/api/set-lambda`);

  onParametersChange('input_f_I',
    (newValue) => { parameters.f_I = newValue },
    `/api/set-fi`);

  onParametersChange('input_f_E',
    (newValue) => { parameters.f_E = newValue },
    `/api/set-fe`);

  onParametersChange('input_node_bandwidth',
    (newValue) => { parameters.inputNodeBandwidth = newValue },
    `/api/set-node-bandwidth`);

  onParametersChange('input_ib_size',
    (newValue) => { parameters.ibSize = newValue },
    `/api/set-ib-size`);

  // activate all tooltips
  // see https://getbootstrap.com/docs/5.0/components/tooltips/
  const tooltipTriggerList = [].slice.call(document.querySelectorAll('[data-bs-toggle="tooltip"]'));
  const tooltipList = tooltipTriggerList.map(function(tooltipTriggerEl) {
    return new bootstrap.Tooltip(tooltipTriggerEl);
  });

  const input_lambda = document.getElementById('input_lambda');
  input_lambda.addEventListener('change', function() {
    parameters.λ = input_lambda.value;
    postJSON(`/api/set-lambda?sessionId=${sessionId}`,
      parseInt(input_lambda.value));
  });

});

/*
 * Add an event listener on the given parameter id.
 *
 * When the value changes `applyNewvalue` is called with this new
 * value, and the new value is sent to the given endpoint.
 *
 * We assume the value `parameterId` refers to is an integer.
 *
 * The query parameter `sessionId=${sessionId}` will be added to the given endpoint.
 */
function onParametersChange(parameterId, applyNewValue, endpoint) {
  const input = document.getElementById(parameterId);
  input.addEventListener('change', function() {
    applyNewValue(input.value);
    postJSON(`${endpoint}?sessionId=${sessionId}`, parseInt(input.value));
  });
}

async function startSimulation() {
  const L = document.getElementById('input_L');
  const λ = document.getElementById('input_lambda');
  const f_I = document.getElementById('input_f_I');
  const f_E = document.getElementById('input_f_E');
  const nodeBandwidth = document.getElementById('input_node_bandwidth');
  const ibSize = document.getElementById('input_ib_size');

  // TODO: perform parameters validation
  parameters = {
    _L: Number(L.value),
    λ: Number(λ.value),
    nodeBandwidth: Number(nodeBandwidth.value),
    ibSize: Number(ibSize.value),
    f_I: Number(f_I.value),
    f_E: Number(f_E.value),
    initialSeed: 9126589237 // TODO: add a field for this
  }

  postJSON(`/api/start-simulation?sessionId=${sessionId}`, parameters);
}

async function stopSimulation() {
  post(`/api/stop-simulation?sessionId=${sessionId}`);
}

function http() {
  return `${window.location.protocol}//${window.location.hostname}:${window.location.port}`;
}

/*
 * GET / POST methods
 */

async function getJSON(endpoint) {
  const url = http() + endpoint;
  const response = await fetch(url);

  if (!response.ok) {
    throw new Error(`Response status: ${response.status}`);
  }

  const json = await response.json();
  return json;
}

async function post(endpoint) {
  try {
    const url = http() + endpoint;
    const response = await fetch(url, {
      method: "POST"
    });

  } catch (error) {
    console.error("Error:", error);
  }
}

async function postJSON(endpoint, data) {
  try {
    const url = http() + endpoint;
    const response = await fetch(url, {
      method: "POST",
      headers: {
        "Content-Type": "application/json",
      },
      body: JSON.stringify(data),
    });

  } catch (error) {
    console.error("Error:", error);
  }
}
