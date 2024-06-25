document.addEventListener('DOMContentLoaded', () => {
  const node = document.getElementById('throughput');

  // throughput chart
  const chart = new Chart(node, {
    title: {
      text: "Leios Blocks throughput"
    },
    data: {
      datasets: [{
        type: 'bar',
        label: "Queue size",
        data: []
      }, {
        type: 'line',
        label: "EB throughput",
        data: []
      }]
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

  ws.onmessage = function(message) {
    if (message.data) {
      const eb = JSON.parse(message.data);

      if (eb.tag == 'ReceivedEB') {

        if (chart.data.datasets[0].data.length > 49) {
          chart.data.datasets[0].data.splice(0, chart.data.datasets[0].data.length - 49);
          chart.data.datasets[1].data.splice(0, chart.data.datasets[1].data.length - 49);
        }

        // TODO: determine the queue size
        chart.data.datasets[0].data.push({ x: eb.receivedEB.eb_slot, y: 0 });
        console.log (eb.receivedEB);
        console.log (eb.receivedEB.eb_slot);

        chart.data.datasets[1].data.push({ x: eb.receivedEB.eb_slot, y: eb.receivedEB.eb_linked_IBs.length });
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
