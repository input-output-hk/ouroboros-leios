document.addEventListener('DOMContentLoaded', () => {
  const node = document.getElementById('throughput');

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
          label: "EB throughput",
          data: [],
	  backgroundColor: '#235FA4',
	  borderColor: '#235FA4',
        },
	{ type: 'bar',
          label: "Queue size",
          data: [],
	  backgroundColor: '#E8F086',
	  borderColor: '#E8F086',
	}
      ]
    },
    options: {
      scales: {
        x: {
          type: 'linear',
          title: {
            text: 'Rounds',
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

      if (logData.tag == 'ReceivedEB') {

        if (chart.data.datasets[0].data.length > 49) {
          chart.data.datasets[0].data.splice(0, chart.data.datasets[0].data.length - 49);
          chart.data.datasets[1].data.splice(0, chart.data.datasets[1].data.length - 49);
        }

	if (logData.receivedEB.eb_linked_IBs.length != 0) {
	  queuedIBs = _.differenceWith(queuedIBs, logData.receivedEB.eb_linked_IBs, _.isEqual);
	}

        chart.data.datasets[0].data.push({ x: logData.receivedEB.eb_slot,
					   y: logData.receivedEB.eb_linked_IBs.length });
        chart.data.datasets[1].data.push({ x: logData.receivedEB.eb_slot, y: queuedIBs.length });

        const minx = chart.data.datasets[0].data[0].x;
        chart.options.scales.x.min = minx;
        chart.options.scales.x.max = minx + 50;
        chart.update();
      }

      if (logData.tag == 'ProducedIB') {
	queuedIBs.push(logData.producedIB);
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
  const lambda = document.getElementById('lambda');
  lambda.addEventListener('change', function() {
    postJSON("http://" + window.location.hostname + ":" +
      window.location.port + "/api/lambda", parseInt(lambda.value));
  });

  const bps = document.getElementById('bps');
  capacity.addEventListener('change', function() {
    postJSON("http://" + window.location.hostname + ":" +
      window.location.port + "/api/node-bandwidth", parseInt(capacity.value));
  });

});

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
