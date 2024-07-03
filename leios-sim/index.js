document.addEventListener('DOMContentLoaded', () => {

  // FIXME: these have to be synchronized with the simulation.
  var parameters = { L: 4,
		     λ: 3
		   }

  function sliceOf(slot) {
    return Math.floor(slot / parameters.L);
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
	{ type: 'line',
          label: "Created IBs",
          data: [],
	  backgroundColor: '#6FDE6E',
	  borderColor: '#6FDE6E',
	},
	{ type: 'line',
          label: "Linked IBs",
          data: [],
	  backgroundColor: '#235FA4',
	  borderColor: '#235FA4',
        },
	{ type: 'line',
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

  // Retrieve simulation data from server.
  const wsPath = window.location.pathname.split('/').slice(0, -1).join('/');
  const ws = new WebSocket("ws://" + window.location.hostname + ":" + window.location.port + wsPath);

  ws.onopen = function() {
    console.log('connected');
  };

  // We will add elements to the queue when we get a log message about
  // a new IB being created. When we receive a log message about a
  // created EB, we will remove the linked IBs inside the EB from the
  // queue.
  var queuedIBs = [];

  ws.onmessage = function(message) {
    if (message.data) {
      const logData = JSON.parse(message.data);

      // Keep only the last 50 entries
      //
      // TODO: find out why the chart won't display properly if this is done after pushing data.
      if (chart.data.datasets[0].data.length > 49) {
        chart.data.datasets[0].data.splice(0, chart.data.datasets[0].data.length - 49);
      }

      if (logData.tag == 'ReceivedEB') {

	if (logData.receivedEB.eb_linked_IBs.length != 0) {
	  queuedIBs = _.differenceWith(queuedIBs, logData.receivedEB.eb_linked_IBs, _.isEqual);
	}

	// We know that future EBs will link IBs whose slots are
	// greater or equal than the slice linked by the current
	// EB. Therefore we can regard all those IBs with smaller
	// slots as *lost*.
	droppedIBs = queuedIBs.filter(ib =>
	  sliceOf (ib.ib_slot) < sliceOf(logData.receivedEB.eb_slot) - (parameters.λ + 1)
	);

	queuedIBs = _.differenceWith(queuedIBs, droppedIBs, _.isEqual);

	var i = chart.data.datasets[1].data.findIndex(p => p.x == logData.receivedEB.eb_slot);
	if (0 <= i) {
	  chart.data.datasets[1].data[i] = {x: logData.receivedEB.eb_slot,
					    y: chart.data.datasets[1].data[i].y + logData.receivedEB.eb_linked_IBs.length};
	} else {
	  chart.data.datasets[1].data.push({ x: logData.receivedEB.eb_slot,
					     y: logData.receivedEB.eb_linked_IBs.length });
	}


        chart.data.datasets[2].data.push({ x: logData.receivedEB.eb_slot,
					   y: droppedIBs.length });

        chart.update();
      }

      if (logData.tag == 'ProducedIB') {
	queuedIBs.push(logData.producedIB);

	var i = chart.data.datasets[0].data.findIndex(p => p.x == logData.producedIB.ib_slot);
	if (0 <= i) {
	  chart.data.datasets[0].data[i] = {x: logData.producedIB.ib_slot, y: chart.data.datasets[0].data[i].y + 1 };
	} else {
	  chart.data.datasets[0].data.push( {x: logData.producedIB.ib_slot, y: 1});
	}

	// Adjust the data range
	const minx = chart.data.datasets[0].data[0].x;
        chart.options.scales.x.min = minx;
        chart.options.scales.x.max = minx + 50;
	chart.update();
      }
    }

  };

  window.onbeforeunload = _ => {
    ws.close();
  };

  ws.onclose = function() {
    console.log('disconnected');
  };

  // handle parameters change
  const input_λ = document.getElementById('input_λ');
  input_λ.addEventListener('change', function() {
    parameters.λ = input_λ.value;
    postJSON("http://" + window.location.hostname + ":" +
      window.location.port + "/api/lambda", parseInt(input_λ.value));
  });

});

async function startSimulation() {
  const L = document.getElementById('input_L');
  const λ = document.getElementById('input_λ');
  console.log(L.value);
  console.log(λ.value);
}

async function stopSimulation() {

}

async function postJSON(url, data) {
  try {
    const response = await fetch(url, {
      method: "POST",
      headers: {
        "Content-Type": "application/json",
      },
      body: JSON.stringify(data),
    });

    const result = await response.json();
    console.log("Success:", result);
  } catch (error) {
    console.error("Error:", error);
  }
}
