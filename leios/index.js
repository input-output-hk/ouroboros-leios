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
      chart.data.datasets[0].data.push({ x: eb.endorsementTimestamp, y: eb.queueSize });
      chart.data.datasets[1].data.push({ x: eb.endorsementTimestamp, y: eb.inputBlocks.length });
      chart.options.scales.x.min = eb.endorsementTimestamp - 50;
      chart.options.scales.x.max = eb.endorsementTimestamp;
      chart.update();
    }
  };

  window.onbeforeunload = _ => {
    ws.close();
  };

});
