// Isabella Benchmarks Visualization

const LANGUAGES = ['haskell', 'ocaml', 'javascript', 'scala'];
const LANGUAGE_COLORS = {
  haskell: '#00ff88',
  ocaml: '#ff7b72',
  javascript: '#a5d6ff',
  scala: '#d2a8ff'
};

const FUNCTIONS = ['inner_prod', 'vec_add', 'mat_vec_mult', 'lwe_encrypt', 'lwe_decrypt'];

let benchmarkData = {};
let chartState = {
  datasets: [],
  sizes: [],
  scale: 'linear',
  margin: { top: 20, right: 30, bottom: 50, left: 70 },
  points: [] // Store point positions for tooltip
};

// Load benchmark data
async function loadBenchmarkData() {
  for (const func of FUNCTIONS) {
    try {
      const response = await fetch(`../bench/data/${func}.json`);
      if (response.ok) {
        benchmarkData[func] = await response.json();
      }
    } catch (e) {
      console.warn(`Could not load ${func}.json:`, e);
      benchmarkData[func] = generateMockData(func);
    }
  }

  if (Object.keys(benchmarkData).length === 0) {
    for (const func of FUNCTIONS) {
      benchmarkData[func] = generateMockData(func);
    }
  }

  updateChart();
  updateStats();
  updateTable();
}

// Generate mock data for demonstration
function generateMockData(func) {
  const sizes = [10, 50, 100, 200, 350, 500, 750];
  const baseMultipliers = {
    inner_prod: 1,
    vec_add: 0.8,
    mat_vec_mult: 5,
    lwe_encrypt: 10,
    lwe_decrypt: 8
  };

  const langMultipliers = {
    haskell: 1.2,
    ocaml: 1.0,
    javascript: 2.5,
    scala: 1.5
  };

  const results = [];

  for (const lang of LANGUAGES) {
    for (const size of sizes) {
      const base = baseMultipliers[func] * langMultipliers[lang];
      const mean = base * size * (1 + Math.random() * 0.2);
      const stdev = mean * 0.1;

      results.push({
        language: lang,
        input_size: size,
        timing: {
          min: mean - stdev * 2,
          max: mean + stdev * 2,
          mean: mean,
          median: mean * (0.95 + Math.random() * 0.1),
          stdev: stdev
        }
      });
    }
  }

  return {
    function: func,
    results: results
  };
}

function formatTime(ms) {
  if (ms < 0.001) return '0';
  if (ms < 1) return ms.toFixed(3);
  if (ms < 10) return ms.toFixed(2);
  if (ms < 100) return ms.toFixed(1);
  return Math.round(ms).toString();
}

// Draw chart
function drawChart(canvas, datasets, sizes, scale) {
  const width = canvas.width;
  const height = canvas.height;
  const ctx = canvas.getContext('2d');
  const margin = chartState.margin;

  // Clear
  ctx.fillStyle = '#111111';
  ctx.fillRect(0, 0, width, height);

  const chartWidth = width - margin.left - margin.right;
  const chartHeight = height - margin.top - margin.bottom;

  // Find max value
  let maxVal = 0;
  datasets.forEach(d => {
    d.data.forEach(v => {
      if (v > maxVal) maxVal = v;
    });
  });
  maxVal = maxVal * 1.1;

  // Scale functions
  const xScale = (i) => margin.left + (i / (sizes.length - 1)) * chartWidth;
  const yScale = scale === 'log'
    ? (v) => margin.top + chartHeight - (Math.log10(v + 1) / Math.log10(maxVal + 1)) * chartHeight
    : (v) => margin.top + chartHeight - (v / maxVal) * chartHeight;

  // Store for tooltip
  chartState.xScale = xScale;
  chartState.yScale = yScale;
  chartState.chartWidth = chartWidth;
  chartState.chartHeight = chartHeight;
  chartState.maxVal = maxVal;

  // Draw grid
  ctx.strokeStyle = '#222222';
  ctx.lineWidth = 1;

  const gridLines = 5;
  for (let i = 0; i <= gridLines; i++) {
    const y = margin.top + (i / gridLines) * chartHeight;
    ctx.beginPath();
    ctx.moveTo(margin.left, y);
    ctx.lineTo(width - margin.right, y);
    ctx.stroke();

    const val = scale === 'log'
      ? Math.pow(10, (1 - i / gridLines) * Math.log10(maxVal + 1)) - 1
      : maxVal * (1 - i / gridLines);
    ctx.fillStyle = '#555555';
    ctx.font = '11px JetBrains Mono';
    ctx.textAlign = 'right';
    ctx.fillText(formatTime(val), margin.left - 10, y + 4);
  }

  // X-axis labels
  ctx.textAlign = 'center';
  sizes.forEach((size, i) => {
    const x = xScale(i);
    ctx.fillStyle = '#555555';
    ctx.fillText(size.toString(), x, height - margin.bottom + 20);
  });

  // Axis labels
  ctx.fillStyle = '#888888';
  ctx.font = '12px JetBrains Mono';
  ctx.textAlign = 'center';
  ctx.fillText('Input Size', margin.left + chartWidth / 2, height - 10);

  ctx.save();
  ctx.translate(15, margin.top + chartHeight / 2);
  ctx.rotate(-Math.PI / 2);
  ctx.fillText('Time (ms)', 0, 0);
  ctx.restore();

  // Clear points array
  chartState.points = [];

  // Draw lines and collect points
  datasets.forEach(dataset => {
    ctx.strokeStyle = dataset.color;
    ctx.lineWidth = 2;
    ctx.beginPath();

    dataset.data.forEach((val, i) => {
      const x = xScale(i);
      const y = yScale(val);

      // Store point for tooltip
      chartState.points.push({
        x, y,
        value: val,
        size: sizes[i],
        language: dataset.label,
        color: dataset.color
      });

      if (i === 0) {
        ctx.moveTo(x, y);
      } else {
        ctx.lineTo(x, y);
      }
    });

    ctx.stroke();

    // Draw points
    ctx.fillStyle = dataset.color;
    dataset.data.forEach((val, i) => {
      const x = xScale(i);
      const y = yScale(val);

      ctx.beginPath();
      ctx.arc(x, y, 4, 0, Math.PI * 2);
      ctx.fill();
    });
  });
}

// Tooltip handling
function initTooltip(canvas) {
  const tooltip = document.getElementById('chart-tooltip');

  canvas.addEventListener('mousemove', (e) => {
    const rect = canvas.getBoundingClientRect();

    // Scale mouse coordinates to canvas internal coordinates
    const scaleX = canvas.width / rect.width;
    const scaleY = canvas.height / rect.height;
    const x = (e.clientX - rect.left) * scaleX;
    const y = (e.clientY - rect.top) * scaleY;

    // Find nearest point
    let nearest = null;
    let minDist = 25; // Threshold distance

    chartState.points.forEach(point => {
      const dist = Math.sqrt(Math.pow(point.x - x, 2) + Math.pow(point.y - y, 2));
      if (dist < minDist) {
        minDist = dist;
        nearest = point;
      }
    });

    if (nearest) {
      tooltip.innerHTML = `
        <div class="tooltip-lang" style="color: ${nearest.color}">${nearest.language}</div>
        <div class="tooltip-value">${formatTime(nearest.value)} ms</div>
        <div class="tooltip-size">size: ${nearest.size}</div>
      `;
      tooltip.style.display = 'block';

      // Position tooltip in display coordinates (not canvas coordinates)
      const displayX = nearest.x / scaleX;
      const displayY = nearest.y / scaleY;

      let tooltipX = displayX + 12;
      let tooltipY = displayY - 40;

      // Keep tooltip in bounds
      if (tooltipX + 100 > rect.width) {
        tooltipX = displayX - 105;
      }
      if (tooltipY < 0) {
        tooltipY = displayY + 15;
      }

      tooltip.style.left = tooltipX + 'px';
      tooltip.style.top = tooltipY + 'px';
    } else {
      tooltip.style.display = 'none';
    }
  });

  canvas.addEventListener('mouseleave', () => {
    tooltip.style.display = 'none';
  });
}

// Update chart
function updateChart() {
  const func = document.getElementById('function-select').value;
  const metric = document.getElementById('metric-select').value;
  const scale = document.getElementById('scale-select').value;

  const data = benchmarkData[func];
  if (!data) return;

  const sizes = [...new Set(data.results.map(r => r.input_size))].sort((a, b) => a - b);

  const datasets = LANGUAGES.map(lang => {
    const langResults = data.results.filter(r => r.language === lang);
    const values = sizes.map(size => {
      const result = langResults.find(r => r.input_size === size);
      return result ? result.timing[metric] : 0;
    });

    return {
      label: lang,
      data: values,
      color: LANGUAGE_COLORS[lang]
    };
  });

  // Store state
  chartState.datasets = datasets;
  chartState.sizes = sizes;
  chartState.scale = scale;

  // Update title
  document.getElementById('chart-title').textContent = func;

  // Update legend
  const legend = document.getElementById('chart-legend');
  legend.innerHTML = datasets.map(d =>
    `<span class="legend-item"><span class="legend-color" style="background:${d.color}"></span>${d.label}</span>`
  ).join('');

  // Get canvas
  const canvas = document.getElementById('benchmark-chart');
  const rect = canvas.parentElement.getBoundingClientRect();
  canvas.width = rect.width;
  canvas.height = 350;

  drawChart(canvas, datasets, sizes, scale);
}

// Update stats
function updateStats() {
  const func = document.getElementById('function-select').value;
  const data = benchmarkData[func];
  if (!data) return;

  const grid = document.getElementById('stats-grid');

  const cards = LANGUAGES.map(lang => {
    const langResults = data.results.filter(r => r.language === lang);
    if (langResults.length === 0) return '';

    const avgMean = langResults.reduce((sum, r) => sum + r.timing.mean, 0) / langResults.length;
    const maxSize = Math.max(...langResults.map(r => r.input_size));
    const maxResult = langResults.find(r => r.input_size === maxSize);

    return `
      <div class="stat-card">
        <div class="stat-header">
          <span class="stat-lang" style="color: ${LANGUAGE_COLORS[lang]}">${lang}</span>
        </div>
        <div class="stat-value">${formatTime(avgMean)} ms</div>
        <div class="stat-label">avg across sizes</div>
        <div class="stat-detail">
          <span>size ${maxSize}:</span>
          <span>${formatTime(maxResult?.timing.mean || 0)} ms</span>
        </div>
      </div>
    `;
  });

  grid.innerHTML = cards.join('');
}

// Update table
function updateTable() {
  const func = document.getElementById('function-select').value;
  const data = benchmarkData[func];
  if (!data) return;

  // Update table title
  document.getElementById('table-title').textContent = `Raw Data - ${func}`;

  const tbody = document.getElementById('table-body');

  const rows = data.results.map(r => `
    <tr>
      <td><span class="lang-badge" style="color: ${LANGUAGE_COLORS[r.language]}">${r.language}</span></td>
      <td>${r.input_size}</td>
      <td>${formatTime(r.timing.min)}</td>
      <td>${formatTime(r.timing.max)}</td>
      <td>${formatTime(r.timing.mean)}</td>
      <td>${formatTime(r.timing.median)}</td>
      <td>${formatTime(r.timing.stdev)}</td>
    </tr>
  `);

  tbody.innerHTML = rows.join('');
}

// Event listeners
document.addEventListener('DOMContentLoaded', () => {
  loadBenchmarkData();

  // Init tooltip
  const canvas = document.getElementById('benchmark-chart');
  initTooltip(canvas);

  document.getElementById('function-select').addEventListener('change', () => {
    updateChart();
    updateStats();
    updateTable();
  });

  document.getElementById('metric-select').addEventListener('change', updateChart);
  document.getElementById('scale-select').addEventListener('change', updateChart);

  window.addEventListener('resize', updateChart);
});
