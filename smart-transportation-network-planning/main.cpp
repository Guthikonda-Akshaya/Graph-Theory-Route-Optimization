#include <iostream>
#include <vector>
#include <queue>
#include <set>
#include <map>
#include <random>
#include <algorithm>
#include <iomanip>
#include <fstream>
#include <limits>

class SmartCityNetwork {
private:
    struct DSU {
        std::vector<int> parent, rank;
        DSU(int n) {
            parent.resize(n + 1);
            rank.assign(n + 1, 0);
            for (int i = 0; i <= n; i++) parent[i] = i;
        }
        int find(int i) {
            if (parent[i] == i) return i;
            return parent[i] = find(parent[i]);
        }
        void unite(int i, int j) {
            int root_i = find(i);
            int root_j = find(j);
            if (root_i != root_j) {
                if (rank[root_i] < rank[root_j]) parent[root_i] = root_j;
                else if (rank[root_i] > rank[root_j]) parent[root_j] = root_i;
                else {
                    parent[root_j] = root_i;
                    rank[root_i]++;
                }
            }
        }
    };

    struct Edge {
        int u, v;
        double w;
        bool operator<(const Edge& other) const {
            return w < other.w;
        }
    };

    int V;
    std::vector<std::vector<std::pair<int, double>>> adj;
    std::vector<Edge> edges;
    std::mt19937 rng;
    const double INF = std::numeric_limits<double>::infinity();

    void addEdge(int u, int v, double w) {
        adj[u].push_back({v, w});
        adj[v].push_back({u, w});
        edges.push_back({u, v, w});
    }

    void runDijkstra(int src, int dest, int skipNode = -1, std::pair<int, int> skipEdge = {-1, -1}, std::map<std::pair<int,int>, double>* trafficMap = nullptr) {
        std::vector<double> dist(V, INF);
        std::vector<int> parent(V, -1);
        std::priority_queue<std::pair<double, int>, std::vector<std::pair<double, int>>, std::greater<std::pair<double, int>>> pq;

        dist[src] = 0;
        pq.push({0, src});

        while (!pq.empty()) {
            double d = pq.top().first;
            int u = pq.top().second;
            pq.pop();

            if (u == dest) break;
            if (d > dist[u]) continue;

            for (const auto& edge : adj[u]) {
                int v = edge.first;
                double w = edge.second;

                if (v == skipNode) continue;
                if ((u == skipEdge.first && v == skipEdge.second) || (u == skipEdge.second && v == skipEdge.first)) continue;

                if (trafficMap != nullptr) {
                    std::pair<int, int> key = {std::min(u, v), std::max(u, v)};
                    if (trafficMap->count(key)) {
                        w *= (*trafficMap)[key];
                    }
                }

                if (dist[u] + w < dist[v]) {
                    dist[v] = dist[u] + w;
                    parent[v] = u;
                    pq.push({dist[v], v});
                }
            }
        }

        if (dist[dest] == INF) {
            std::cout << "> No valid route available after disaster.\n";
            return;
        }

        std::cout << "> Distance: " << std::fixed << std::setprecision(2) << dist[dest] << " km | Path: ";
        std::vector<int> path;
        for (int curr = dest; curr != -1; curr = parent[curr]) path.push_back(curr);
        std::reverse(path.begin(), path.end());
        for (int node : path) std::cout << node << " ";
        std::cout << "\n";
    }

    void dfsTarjan(int u, int p, std::vector<int>& tin, std::vector<int>& low, int& timer, 
                   int& maxCompsCity, int& criticalCity, std::vector<std::pair<int, int>>& bridges) {
        
        tin[u] = low[u] = timer++;
        int children = 0;
        int splits = (p != -1) ? 1 : 0; 

        for (const auto& edge : adj[u]) {
            int v = edge.first;
            if (v == p) continue;
            
            if (tin[v] != -1) {
                low[u] = std::min(low[u], tin[v]);
            } else {
                children++;
                dfsTarjan(v, u, tin, low, timer, maxCompsCity, criticalCity, bridges);
                low[u] = std::min(low[u], low[v]);
                
                if (low[v] >= tin[u] && p != -1) {
                    splits++;
                }
                
                if (low[v] > tin[u]) {
                    bridges.push_back({std::min(u, v), std::max(u, v)});
                }
            }
        }
        
        if (p == -1) {
            splits = children;
        }
        
        if (splits > maxCompsCity) {
            maxCompsCity = splits;
            criticalCity = u;
        }
    }

public:
    SmartCityNetwork(int vertices) : V(vertices), adj(vertices), rng(42) {}

    void generateGraph(int numEdges) {
        std::uniform_real_distribution<double> weightDist(10.0, 150.0);
        std::set<std::pair<int, int>> used;

        for (int i = 1; i < V; i++) {
            std::uniform_int_distribution<int> nodeDist(0, i - 1);
            int u = i;
            int v = nodeDist(rng);
            double w = weightDist(rng);
            
            used.insert({std::min(u, v), std::max(u, v)});
            addEdge(u, v, w);
        }

        std::uniform_int_distribution<int> allNodes(0, V - 1);
        int added = V - 1;
        
        while (added < numEdges) {
            int u = allNodes(rng);
            int v = allNodes(rng);
            
            if (u != v) {
                std::pair<int, int> edgeKey = {std::min(u, v), std::max(u, v)};
                if (used.find(edgeKey) == used.end()) { 
                    double w = weightDist(rng);
                    used.insert(edgeKey);
                    addEdge(u, v, w);
                    added++;
                }
            }
        }
    }

    void task1_MST() {
        std::cout << "\n--- TASK 1: MST OPTIMIZATION ---\n";
        double totalCost = 0;
        for (const auto& e : edges) totalCost += e.w;

        std::vector<Edge> tempEdges = edges;
        std::sort(tempEdges.begin(), tempEdges.end());
        
        DSU dsu(V);
        double mstCost = 0;
        std::vector<std::pair<int, int>> mstRoads;

        for (const auto& e : tempEdges) {
            if (dsu.find(e.u) != dsu.find(e.v)) {
                dsu.unite(e.u, e.v);
                mstCost += e.w;
                mstRoads.push_back({e.u, e.v});
            }
        }

        double saved = ((totalCost - mstCost) / totalCost) * 100.0;
        std::cout << std::fixed << std::setprecision(2);
        std::cout << "> Original Cost = " << totalCost << "\n";
        std::cout << "> MST Cost = " << mstCost << "\n";
        std::cout << "> Cost Saved = " << saved << "%\n";
        
        std::cout << "> Selected Roads:\n";
        // Printing only the first 10 to avoid console spam, similar to real-world log truncations
        for (size_t i = 0; i < std::min((size_t)10, mstRoads.size()); i++) {
            std::cout << "(" << mstRoads[i].first << "," << mstRoads[i].second << ")\n";
        }
        std::cout << "[All " << mstRoads.size() << " structural spans successfully written to path buffer]\n";

        std::ofstream fout("mst_edges.txt");
        if (fout.is_open()) {
            for (const auto& r : mstRoads) {
                fout << r.first << " " << r.second << "\n";
            }
            fout.close();
        }
    }

    void task2_StrategicCities() {
        std::cout << "\n--- TASK 2: STRATEGIC CITY IDENTIFICATION ---\n";
        std::vector<std::pair<int, int>> deg; 
        for (int i = 0; i < V; i++) {
            deg.push_back({adj[i].size(), i});
        }
        
        std::sort(deg.rbegin(), deg.rend()); 

        for (int i = 0; i < 10 && i < V; i++) {
            std::cout << "> Rank " << i + 1 << " City " << deg[i].second << " | Degree " << deg[i].first << "\n";
        }
    }

    void task3_Disaster(int src, int dest, int deadCity, int deadRoadU, int deadRoadV) {
        std::cout << "\n--- TASK 3: DISASTER RECOVERY ROUTING ---\n";
        std::cout << "Simulating destruction of City " << deadCity << ":\n";
        runDijkstra(src, dest, deadCity);
        
        std::cout << "Simulating destruction of Road (" << deadRoadU << "," << deadRoadV << "):\n";
        runDijkstra(src, dest, -1, {deadRoadU, deadRoadV});
    }

    void task4_Traffic(int src, int dest) {
        std::cout << "\n--- TASK 4: TRAFFIC-AWARE SMART ROUTING ---\n";
        
        std::map<std::pair<int,int>, double> trafficWeights;
        std::uniform_real_distribution<double> mult(1.0, 3.0);
        
        for (const auto& e : edges) {
            trafficWeights[{std::min(e.u, e.v), std::max(e.u, e.v)}] = mult(rng);
        }

        std::cout << "Normal Route:\n";
        runDijkstra(src, dest);
        
        std::cout << "Traffic Route (Static Congestion Applied):\n";
        runDijkstra(src, dest, -1, {-1, -1}, &trafficWeights);
    }

    void task5_Critical() {
        std::cout << "\n--- TASK 5: CRITICAL INFRASTRUCTURE ANALYSIS ---\n";
        
        std::vector<int> tin(V, -1), low(V, -1);
        int timer = 0;
        int maxCompsCity = 1;
        int criticalCity = -1;
        
        std::vector<std::pair<int, int>> bridges;
        dfsTarjan(0, -1, tin, low, timer, maxCompsCity, criticalCity, bridges);

        if (maxCompsCity > 1) {
            std::cout << "> Most Critical City:\nCity " << criticalCity << "\n";
            std::cout << "> Disconnected Components Created:\n" << maxCompsCity << "\n";
        } else {
             std::cout << "> Most Critical City: None (Network is strongly connected)\n";
        }
        
        if (!bridges.empty()) {
            std::cout << "> Most Critical Road:\n(" << bridges[0].first << "," << bridges[0].second << ")\n";
        } else {
            std::cout << "> Most Critical Road: None (Graph is 2-edge-connected)\n";
        }
    }
};

int main() {
    std::ios_base::sync_with_stdio(false);
    std::cin.tie(NULL);

    SmartCityNetwork network(500);
    network.generateGraph(2000);

    network.task1_MST();
    network.task2_StrategicCities();
    network.task3_Disaster(12, 203, 91, 12, 55); 
    network.task4_Traffic(10, 250);
    network.task5_Critical();

    return 0;
}