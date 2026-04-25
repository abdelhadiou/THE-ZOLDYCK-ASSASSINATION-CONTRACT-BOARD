/**
 * Zoldyck Optimization Engine
 * Core module: contract selection, travel routing, skill progression, uncertainty handling
 */

const fs = require("fs");
const path = require("path");

// ─── Data Loading ─────────────────────────────────────────────────────────────

function loadData(contractsPath, mapPath, profilePath) {
  const contracts = JSON.parse(fs.readFileSync(contractsPath, "utf-8"));
  const map = JSON.parse(fs.readFileSync(mapPath, "utf-8"));
  const profile = JSON.parse(fs.readFileSync(profilePath, "utf-8"));
  return { contracts, map, profile };
}

// ─── Travel Utilities ─────────────────────────────────────────────────────────

function getCityId(map, cityName) {
  if (!map || !map.cities) return cityName;
  const city = map.cities.find(c => c.name === cityName || c.id === cityName);
  return city ? city.id : cityName;
}

/**
 * Dijkstra shortest path between two cities
 */
function shortestPath(map, startCity, endCity) {
  const startId = getCityId(map, startCity);
  const endId = getCityId(map, endCity);
  if (startId === endId) return { distance: 0, path: [startId] };

  const dist = {};
  const prev = {};
  const unvisited = new Set(map.cities.map(c => c.id));

  for (const city of unvisited) dist[city] = Infinity;
  dist[startId] = 0;

  while (unvisited.size > 0) {
    let current = null;
    let minDist = Infinity;
    
    for (const city of unvisited) {
      if (dist[city] < minDist) {
        minDist = dist[city];
        current = city;
      }
    }

    if (current === null || current === endId) break;
    unvisited.delete(current);

    const neighbors = map.travel_times[current] || {};
    for (const [neighbor, weight] of Object.entries(neighbors)) {
      if (!unvisited.has(neighbor)) continue;
      const alt = dist[current] + weight;
      if (alt < dist[neighbor]) {
        dist[neighbor] = alt;
        prev[neighbor] = current;
      }
    }
  }

  const path = [];
  let curr = endId;
  while (curr) {
    path.unshift(curr);
    curr = prev[curr];
  }
  return { distance: dist[endId], path };
}

function getTravelTime(map, fromCity, toCity) {
  const fromId = getCityId(map, fromCity);
  const toId = getCityId(map, toCity);
  if (fromId === toId) return 0;
  
  return shortestPath(map, fromId, toId).distance;
}

// ─── Skill Checks ─────────────────────────────────────────────────────────────

function meetsSkillRequirements(skills, required) {
  return Object.entries(required).every(
    ([skill, level]) => (skills[skill] ?? 0) >= level
  );
}

function getAccessibleContracts(contracts, skills, completedIds) {
  return contracts.filter(
    (c) =>
      !completedIds.includes(c.id) &&
      meetsSkillRequirements(skills, c.required_skills)
  );
}

// ─── Uncertainty Simulation ────────────────────────────────────────────────────

function rollComplication(contract, rng) {
  if (!contract.has_complication) return false;
  return rng() < 0.2;
}

function detectTrap(contract) {
  return contract.is_trap;
}

function effectiveExecutionDays(contract, complicated) {
  return complicated
    ? Math.ceil(contract.execution_days * 1.5)
    : contract.execution_days;
}

// ─── Scoring / Heuristics ─────────────────────────────────────────────────────

function scoreContract(contract, currentDay, currentCity, map, skills, reputationMultiplier) {
  const travelDays = getTravelTime(map, currentCity, contract.city);
  const arrivalDay = currentDay + travelDays;

  if (arrivalDay >= contract.deadline_day) return -Infinity;

  const daysRemaining = contract.deadline_day - arrivalDay;
  const totalDaysNeeded = travelDays + contract.execution_days;
  if (totalDaysNeeded > daysRemaining + contract.execution_days) return -Infinity;

  const effectiveGold = contract.gold * reputationMultiplier;
  const goldPerDay = effectiveGold / (totalDaysNeeded + 1);

  const skillValue = Object.values(contract.skill_rewards).reduce((a, b) => a + b, 0) * 500;
  const urgencyBonus = Math.max(0, 50 - daysRemaining) * 10;
  const repValue = contract.reputation_reward * 100;
  const trapPenalty = contract.is_trap ? 500 : 0;

  return goldPerDay + skillValue / (totalDaysNeeded + 1) + urgencyBonus + repValue - trapPenalty;
}

// ─── TSP-like Route Optimizer (Greedy Nearest Deadline) ───────────────────────

function optimizeRoute(activeContracts, currentCity, currentDay, map) {
  const remaining = [...activeContracts];
  const route = [];
  let city = currentCity;
  let day = currentDay;

  while (remaining.length > 0) {
    let best = null;
    let bestScore = -Infinity;

    for (const contract of remaining) {
      const travel = getTravelTime(map, city, contract.city);
      const arrival = day + travel;
      if (arrival >= contract.deadline_day) continue; 

      const effectiveDeadline = contract.deadline_day - contract.execution_days;
      const score = 1000 - effectiveDeadline + (1 / (travel + 1)) * 10;
      if (score > bestScore) {
        bestScore = score;
        best = contract;
      }
    }

    if (!best) {
      for (const c of remaining) route.push({ contract: c, feasible: false });
      break;
    }

    const travel = getTravelTime(map, city, best.city);
    const arrival = day + travel;
    route.push({ contract: best, travel, arrivalDay: arrival, feasible: true });
    day = arrival + best.execution_days;
    city = best.city;
    remaining.splice(remaining.indexOf(best), 1);
  }

  return route;
}

// ─── Main Simulation Loop ──────────────────────────────────────────────────────

function runSimulation(contracts, map, profile, rng = Math.random) {
  const state = {
    day: profile.current_day,
    city: getCityId(map, profile.starting_city),
    gold: profile.gold,
    reputation: profile.reputation,
    skills: { ...profile.skills },
    activeContracts: [],
    completedContracts: [],
    failedContracts: [],
    abandonedContracts: [],
    timeline: [],
    skillLog: [],
  };

  const reputationMultiplier = () =>
    Math.pow(0.9, state.failedContracts.length + state.abandonedContracts.length);

  const log = (msg) => state.timeline.push({ day: state.day, city: state.city, msg });

  const allContractIds = () => [
    ...state.completedContracts.map((c) => c.id),
    ...state.failedContracts.map((c) => c.id),
    ...state.abandonedContracts.map((c) => c.id),
    ...state.activeContracts.map((c) => c.id),
  ];

  function acceptPhase() {
    while (
      state.activeContracts.length < profile.max_active_contracts &&
      state.day < profile.total_days
    ) {
      const accessible = getAccessibleContracts(contracts, state.skills, allContractIds());
      if (accessible.length === 0) break;

      const scored = accessible
        .map((c) => ({
          contract: c,
          score: scoreContract(c, state.day, state.city, map, state.skills, reputationMultiplier()),
        }))
        .filter((x) => x.score > -Infinity)
        .sort((a, b) => b.score - a.score);

      if (scored.length === 0) break;

      const toAccept = scored.slice(0, profile.max_active_contracts - state.activeContracts.length);

      for (const { contract } of toAccept) {
        if (detectTrap(contract)) {
          log(`⚠️  TRAP DETECTED: "${contract.name}" in ${contract.city}. Abandoning. Reputation -1.`);
          state.abandonedContracts.push(contract);
          state.reputation = Math.max(0, state.reputation - 1);
          continue;
        }
        state.activeContracts.push(contract);
        log(`📋 ACCEPTED: "${contract.name}" → ${contract.city} (Gold: ${contract.gold}, Deadline: Day ${contract.deadline_day})`);
      }

      if (toAccept.length === 0) break;
    }
  }

  function executePhase() {
    if (state.activeContracts.length === 0) return;

    const route = optimizeRoute(state.activeContracts, state.city, state.day, map);

    for (const stop of route) {
      const { contract, travel, arrivalDay, feasible } = stop;

      if (!feasible || arrivalDay === undefined) {
        log(`❌ FAILED (infeasible route): "${contract.name}"`);
        state.failedContracts.push(contract);
        state.reputation = Math.max(0, state.reputation - 1);
        continue;
      }

      if (travel > 0) log(`✈️  TRAVELING to ${contract.city} (${travel} days)`);
      state.day = arrivalDay;
      state.city = getCityId(map, contract.city);

      if (state.day >= contract.deadline_day) {
        log(`❌ FAILED (missed deadline Day ${contract.deadline_day}): "${contract.name}"`);
        state.failedContracts.push(contract);
        state.reputation = Math.max(0, state.reputation - 1);
        continue;
      }

      const complicated = rollComplication(contract, rng);
      const execDays = effectiveExecutionDays(contract, complicated);
      if (complicated) {
        log(`⚡ COMPLICATION on "${contract.name}"! Execution takes ${execDays} days instead of ${contract.execution_days}.`);
      }

      state.day += execDays;

      if (state.day > profile.total_days) {
        log(`❌ FAILED (ran out of days): "${contract.name}"`);
        state.failedContracts.push(contract);
        state.reputation = Math.max(0, state.reputation - 1);
        continue;
      }

      const goldEarned = Math.floor(contract.gold * reputationMultiplier());
      state.gold += goldEarned;
      state.reputation += contract.reputation_reward;
      state.completedContracts.push(contract);

      log(`✅ COMPLETED: "${contract.name}" on Day ${state.day}. Gold +${goldEarned} (total: ${state.gold}). Rep: ${state.reputation}`);

      const gained = [];
      for (const [skill, amount] of Object.entries(contract.skill_rewards)) {
        state.skills[skill] = (state.skills[skill] ?? 0) + amount;
        gained.push(`${skill} → ${state.skills[skill]}`);
      }
      if (gained.length > 0) {
        log(`🎯 SKILLS GAINED from "${contract.name}": ${gained.join(", ")}`);
        state.skillLog.push({
          day: state.day,
          contract: contract.name,
          skills: { ...state.skills },
          gained: contract.skill_rewards,
        });
      }
    }
    state.activeContracts = [];
  }

  while (state.day < profile.total_days) {
    const prevCompleted = state.completedContracts.length;
    acceptPhase();
    if (state.activeContracts.length === 0) break;
    executePhase();
    if (state.completedContracts.length === prevCompleted && state.activeContracts.length === 0) break;
  }

  log(`🏁 SIMULATION ENDED on Day ${state.day}. Final gold: ${state.gold}. Reputation: ${state.reputation}.`);
  return state;
}

// ─── Report Generators ────────────────────────────────────────────────────────

function generateOptimalPathReport(state, profile) {
  return [
    "═══════════════════════════════════════════════════════════",
    "       OPTIMAL PATH REPORT — ZOLDYCK CONTRACT BOARD",
    "═══════════════════════════════════════════════════════════",
    `Operative: ${profile.name}`,
    `Starting City: ${profile.starting_city}`,
    `Total Days Available: ${profile.total_days}`,
    "───────────────────────────────────────────────────────────",
    "DAY-BY-DAY TIMELINE",
    "───────────────────────────────────────────────────────────",
    ...state.timeline.map((e) => `[Day ${String(e.day).padStart(3, "0")}] ${e.msg}`),
    "───────────────────────────────────────────────────────────",
    "FINAL SUMMARY",
    "───────────────────────────────────────────────────────────",
    `Contracts Completed : ${state.completedContracts.length}`,
    `Contracts Failed    : ${state.failedContracts.length}`,
    `Contracts Abandoned : ${state.abandonedContracts.length}`,
    `Final Gold          : ${state.gold}`,
    `Final Reputation    : ${state.reputation}`,
    "═══════════════════════════════════════════════════════════",
  ].join("\n");
}

function generateSkillProgressionLog(state, profile) {
  const lines = [
    "═══════════════════════════════════════════════════════════",
    "      SKILL PROGRESSION LOG — ZOLDYCK CONTRACT BOARD",
    "═══════════════════════════════════════════════════════════",
    `Operative: ${profile.name}`,
    "",
    "STARTING SKILLS:",
    ...Object.entries(profile.skills).map(([s, v]) => `  ${s.padEnd(12)}: ${v}`),
    "───────────────────────────────────────────────────────────",
  ];

  for (const entry of state.skillLog) {
    lines.push(`[Day ${String(entry.day).padStart(3, "0")}] After completing: "${entry.contract}"`);
    lines.push(`  Gained: ${Object.entries(entry.gained).map(([s, v]) => `+${v} ${s}`).join(", ")}`);
    lines.push(`  New Skill Levels: ${Object.entries(entry.skills).map(([s, v]) => `${s}=${v}`).join(", ")}`);
    lines.push("");
  }
  lines.push("═══════════════════════════════════════════════════════════");
  return lines.join("\n");
}

function generateStrategyDocument() {
  return `═══════════════════════════════════════════════════════════
         STRATEGY DOCUMENT — ZOLDYCK OPTIMIZATION ENGINE
═══════════════════════════════════════════════════════════

1. CONTRACT SELECTION ALGORITHM
─────────────────────────────────────────────────────────
The engine uses a multi-factor greedy scoring heuristic to
select contracts at each decision point.

Scoring Formula:
  score = goldPerDay
        + skillValuePerDay     (each skill point ≈ 500 gold)
        + urgencyBonus         (deadline pressure reward)
        + reputationValue      (rep * 100)
        - trapPenalty          (traps: -500 expected cost)
...`;
}

// ─── Entry Point ──────────────────────────────────────────────────────────────

function main() {
  const args = process.argv.slice(2);
  const contractsPath = args[0] || path.join(__dirname, "contracts.json");
  const mapPath = args[1] || path.join(__dirname, "map.json");
  const profilePath = args[2] || path.join(__dirname, "profile.json");
  const outputDir = args[3] || path.join(__dirname, "output");

  console.log("🗡️  ZOLDYCK OPTIMIZATION ENGINE STARTING...\n");

  const { contracts, map, profile } = loadData(contractsPath, mapPath, profilePath);

  let seed = 42;
  const seededRng = () => {
    seed = (seed * 1664525 + 1013904223) & 0xffffffff;
    return (seed >>> 0) / 0x100000000;
  };

  const state = runSimulation(contracts, map, profile, seededRng);

  if (!fs.existsSync(outputDir)) fs.mkdirSync(outputDir, { recursive: true });

  fs.writeFileSync(path.join(outputDir, "optimal_path_report.txt"), generateOptimalPathReport(state, profile));
  fs.writeFileSync(path.join(outputDir, "skill_progression_log.txt"), generateSkillProgressionLog(state, profile));
  fs.writeFileSync(path.join(outputDir, "strategy_document.txt"), generateStrategyDocument());
  fs.writeFileSync(path.join(outputDir, "simulation_state.json"), JSON.stringify(state, null, 2));

  console.log(`\n✅ Reports written to: ${outputDir}`);
  console.log(`💰 FINAL GOLD: ${state.gold}`);
  console.log(`🏆 REPUTATION: ${state.reputation}`);
  console.log(`📋 CONTRACTS COMPLETED: ${state.completedContracts.length}`);
}

if (require.main === module) {
  main();
}

module.exports = { loadData, runSimulation, scoreContract, optimizeRoute, shortestPath, getTravelTime, meetsSkillRequirements, getAccessibleContracts };
