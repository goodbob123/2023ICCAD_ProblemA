
#include <stdio.h>

#include "./SAT/test/sat.h"
// #include "./SAT/sat.h"
#include "bmatchSolver.h"
extern "C" {
#include "aiger.h"
}

#include <time.h>

#include <cstring>
#include <fstream>
#include <iostream>
#include <set>
#include <sstream>
#include <string>
#include <unordered_map>
#include <vector>
using namespace std;
////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////
#if defined(ABC_NAMESPACE)
namespace ABC_NAMESPACE {
#elif defined(__cplusplus)
extern "C" {
#endif

////////////////////////////////////
// parser
////////////////////////////////////

double START;

constexpr unsigned int str2int(const char* str, int h = 0) {
    return !str[h] ? 5381 : (str2int(str, h + 1) * 33) ^ str[h];
}

void parser(string in_filename, string out_filename) {
    string line, buf;
    ifstream in_file(in_filename);
    ofstream out_file(out_filename);
    // cerr<<in_filename<<" "<<tag<<endl;

    // Module
    // read
    std::getline(in_file, line);
    if (line.find("module") == string::npos) {
        cerr << "module not found" << endl;
        return;
    }
    buf = line;
    while (line.find(";") == string::npos) {
        std::getline(in_file, line);
        buf += line;
    }
    // replace name
    int pos = buf.find("("), cut_pos;
    while (1) {
        pos = buf.find(" ", pos) + 1;
        if (pos == -1) {
            cerr << "file format error" << endl
                 << buf << endl;
            return;
        };

        // buf.insert(pos, tag);
        pos = buf.find(",", pos);
        if (pos == -1) {
            break;
        };
    }
    out_file << buf << endl;
    buf.clear();

    // Input
    // read
    std::getline(in_file, line);
    if (line.find("input") == string::npos) {
        cerr << "input not found" << endl;
        return;
    }
    buf = line;
    while (line.find(";") == string::npos) {
        std::getline(in_file, line);
        buf += line;
    }
    // replace name
    pos = buf.find("input");
    while (1) {
        pos = buf.find(" ", pos) + 1;
        if (pos == -1) {
            cerr << "file format error" << endl
                 << buf << endl;
            return;
        };

        // buf.insert(pos, tag);
        pos = buf.find(",", pos);
        if (pos == -1) {
            break;
        };
    }
    out_file << buf << endl;
    buf.clear();

    // Output
    // read
    std::getline(in_file, line);
    if (line.find("output") == string::npos) {
        cerr << "output not found" << endl;
        return;
    }
    buf = line;
    while (line.find(";") == string::npos) {
        std::getline(in_file, line);
        buf += line;
    }
    // replace name
    pos = buf.find("output");
    while (1) {
        pos = buf.find(" ", pos) + 1;
        if (pos == -1) {
            cerr << "file format error" << endl
                 << buf << endl;
            return;
        };

        // buf.insert(pos, tag);
        pos = buf.find(",", pos);
        if (pos == -1) {
            break;
        };
    }
    out_file << buf << endl;
    buf.clear();

    // Wire
    // read
    std::getline(in_file, line);
    if (line.find("wire") == string::npos) {
        cerr << "wire not found" << endl;
        return;
    }
    buf = line;
    while (line.find(";") == string::npos) {
        std::getline(in_file, line);
        buf += line;
    }
    // replace name
    pos = buf.find("wire");
    while (1) {
        pos = buf.find(" ", pos) + 1;
        if (pos == -1) {
            cerr << "file format error" << endl
                 << buf << endl;
            return;
        };

        // buf.insert(pos, tag);
        pos = buf.find(",", pos);
        if (pos == -1) {
            break;
        };
    }
    out_file << buf << endl;
    buf.clear();

    // Gate
    // read
    while (1) {
        std::getline(in_file, buf);
        if (buf.find("endmodule") != string::npos) {
            out_file << "endmodule" << endl;
            return;
        }

        // assign gate including (and, or, nand, nor, not, xor, xnor, buf)
        pos = buf.find_first_not_of(" ");
        string gate_type = buf.substr(pos, (buf.find(" ", pos) - pos)), var1, var2, var3;
        pos = buf.find("(");

        // var1
        pos = buf.find(" ", pos) + 1;
        cut_pos = buf.find_first_of(" ", pos) - pos;
        if (pos == -1) {
            cerr << "var1 format error" << endl
                 << buf << endl;
            return;
        };
        var1 = buf.substr(pos, cut_pos);
        // if(var1 != "1'b0" && var1 != "1'b1") var1 = tag + var1;

        // var2
        pos = buf.find(", ", pos) + 2;
        cut_pos = buf.find_first_of(" ", pos) - pos;
        if (pos == -1) {
            cerr << "var2 format error" << endl
                 << buf << endl;
            return;
        };
        var2 = buf.substr(pos, cut_pos);
        // if(var2 != "1'b0" && var2 != "1'b1") var2 = tag + var2;

        // var3
        pos = buf.find(", ", pos);
        if (pos != -1) {
            pos += 2;
            cut_pos = buf.find_first_of(" ", pos) - pos;
            var3 = buf.substr(pos, cut_pos);
            // if(var3 != "1'b0" && var3 != "1'b1") var3 = tag + var3;
        }

        stringstream ss;
        switch (str2int(gate_type.c_str())) {
            case str2int("and"):
                ss << "assign " << var1 << " = " << var2 << " & " << var3 << ";\n";
                break;

            case str2int("or"):
                ss << "assign " << var1 << " = " << var2 << " | " << var3 << ";\n";
                break;

            case str2int("nand"):
                ss << "assign " << var1 << " = ~(" << var2 << " & " << var3 << ");\n";
                break;

            case str2int("nor"):
                ss << "assign " << var1 << " = ~(" << var2 << " | " << var3 << ");\n";
                break;

            case str2int("not"):
                ss << "assign " << var1 << " = ~" << var2 << ";\n";
                break;

            case str2int("xor"):
                ss << "assign " << var1 << " = " << var2 << " ^ " << var3 << ";\n";
                break;

            case str2int("xnor"):
                ss << "assign " << var1 << " = ~(" << var2 << " ^ " << var3 << ");\n";
                break;

            case str2int("buf"):
                ss << "assign " << var1 << " = " << var2 << ";\n";
                break;

            default:
                cerr << "gate type \"" << gate_type << "\" not found" << endl;
                return;
                break;
        }
        // cerr<<ss.str();
        out_file << ss.str();
    }
}

////////////////////////////////////
// gv
////////////////////////////////////

// procedures to start and stop the ABC framework
// (should be called before and after the ABC procedures are called)
void Abc_Start();
void Abc_Stop();

// procedures to get the ABC framework and execute commands in it
typedef struct Abc_Frame_t_ Abc_Frame_t;

Abc_Frame_t* Abc_FrameGetGlobalFrame();
int Cmd_CommandExecute(Abc_Frame_t* pAbc, const char* sCommand);

#if defined(ABC_NAMESPACE)
}
using namespace ABC_NAMESPACE;
#elif defined(__cplusplus)
}
#endif

void write_aig() {
    Abc_Frame_t* pAbc;
    char Command[1000];
    clock_t clk;
    //////////////////////////////////////////////////////////////////////////
    // start the ABC framework
    Abc_Start();
    pAbc = Abc_FrameGetGlobalFrame();

    clk = clock();
    //////////////////////////////////////////////////////////////////////////
    // read the file

    sprintf(Command, "read_verilog %s", "1.v");
    if (Cmd_CommandExecute(pAbc, Command)) {
        fprintf(stdout, "Cannot execute command \"%s\".\n", Command);
        return;
    } else {
        cout << "read success!" << endl;
    }

    sprintf(Command, "strash");
    if (Cmd_CommandExecute(pAbc, Command)) {
        fprintf(stdout, "Cannot execute command \"%s\".\n", Command);
        return;
    } else {
        cout << "success strash!" << endl;
    }

    sprintf(Command, "write_aiger -s %s", "1.aig");
    if (Cmd_CommandExecute(pAbc, Command)) {
        fprintf(stdout, "Cannot execute command \"%s\".\n", Command);
        return;
    } else {
        cout << "success write!" << endl;
    }

    sprintf(Command, "write_aiger %s", "circuit_1.aig");
    if (Cmd_CommandExecute(pAbc, Command)) {
        fprintf(stdout, "Cannot execute command \"%s\".\n", Command);
        return;
    } else {
        cout << "success write!" << endl;
    }

    // func support
    sprintf(Command, "print_supp -w");
    if (Cmd_CommandExecute(pAbc, Command)) {
        fprintf(stdout, "Cannot execute command \"%s\".\n", Command);
        return;
    } else {
        cout << "success print_supp !" << endl;
    }

    sprintf(Command, "read_verilog %s", "2.v");
    if (Cmd_CommandExecute(pAbc, Command)) {
        fprintf(stdout, "Cannot execute command \"%s\".\n", Command);
        return;
    } else {
        cout << "read success!" << endl;
    }

    sprintf(Command, "strash");
    if (Cmd_CommandExecute(pAbc, Command)) {
        fprintf(stdout, "Cannot execute command \"%s\".\n", Command);
        return;
    } else {
        cout << "success strash!" << endl;
    }

    sprintf(Command, "write_aiger -s %s", "2.aig");
    if (Cmd_CommandExecute(pAbc, Command)) {
        fprintf(stdout, "Cannot execute command \"%s\".\n", Command);
        return;
    } else {
        cout << "success write!" << endl;
    }

    sprintf(Command, "write_aiger %s", "circuit_2.aig");
    if (Cmd_CommandExecute(pAbc, Command)) {
        fprintf(stdout, "Cannot execute command \"%s\".\n", Command);
        return;
    } else {
        cout << "success write!" << endl;
    }

    // func support
    sprintf(Command, "print_supp -w");
    if (Cmd_CommandExecute(pAbc, Command)) {
        fprintf(stdout, "Cannot execute command \"%s\".\n", Command);
        return;
    } else {
        cout << "success print_supp !" << endl;
    }
    //////////////////////////////////////////////////////////////////////////
    // stop the ABC framework
    Abc_Stop();
}

////////////////////////////////////
// aigvar to name mapping
////////////////////////////////////

////////////////////////////////////
// aigvar to name mapping
////////////////////////////////////

struct aig_map {
    int var;
    string name;
};

void mapping(const char* in_filename, ofstream& out_file) {
    vector<aig_map> input, output;
    string line, buf;
    stringstream ss;
    ifstream in_file(in_filename);

    // get num_PI num_PO
    int nPI, nPO;
    getline(in_file, line);
    ss << line;
    ss >> buf;
    ss << line;
    ss >> buf;
    ss << line;
    ss >> buf;
    // cout<<buf<<endl;
    nPI = stoi(buf);
    ss << line;
    ss >> buf;
    ss << line;
    ss >> buf;
    // cout<<buf<<endl;
    nPO = stoi(buf);

    // get PI_var
    for (int i = 0; i < nPI; i++) {
        getline(in_file, line);
        aig_map temp;
        // cout<<"PI "<<i<<" "<<line<<endl;
        temp.var = stoi(line);
        input.push_back(temp);
    }

    // get PO_var
    for (int i = 0; i < nPO; i++) {
        getline(in_file, line);
        aig_map temp;
        // cout<<"PO "<<i<<" "<<line<<endl;
        temp.var = stoi(line);
        output.push_back(temp);
    }

    while (line.find("i") == string::npos) {
        getline(in_file, line);
    }

    line = line.substr(line.find(" ") + 1);
    input[0].name = line;
    for (int i = 1; i < nPI; i++) {
        getline(in_file, line);
        line = line.substr(line.find(" ") + 1);
        input[i].name = line;
    }

    for (int i = 0; i < nPO; i++) {
        getline(in_file, line);
        line = line.substr(line.find(" ") + 1);
        output[i].name = line;
    }

    for (int i = 0; i < nPI; i++) {
        out_file << in_filename[strlen(in_filename) - 5] << " input " << input[i].name << " " << input[i].var << endl;
    }
    for (int i = 0; i < nPO; i++) {
        out_file << in_filename[strlen(in_filename) - 5] << " output " << output[i].name << " " << output[i].var << endl;
    }
    in_file.close();
}

////////////////////////////////////
// main
////////////////////////////////////

int main(int argc, char* argv[]) {
    if(argc!=3){
        cerr<<"Wrong input format, please follow the example below. "<<endl;
        cerr<<"./bmatch <CAD_testdata/case01/input> <match>"<<endl;
        exit(0);
    }
    // argument
    START = clock();
    char *input = argv[1], *match = argv[2];
    string circuit_file1, circuit_file2, line, buf = "";

    // open input
    ifstream input_file(input);
    getline(input_file, line);
    buf = buf + line;
    circuit_file1 = line;
    getline(input_file, line);
    buf = buf + line;
    while (line.find(".v") == string::npos) {
        getline(input_file, line);
        buf = buf + line;
    }
    circuit_file2 = line;
    while (getline(input_file, line)) {
        buf = buf + line;
    }
    // cerr<<"buf "<<buf<<endl;

    // cout<<circuit_file1<<" "<<circuit_file2<<endl;
    // delete redundant file
    remove("1.v");
    remove("2.v");
    remove("1.aig");
    remove("2.aig");
    remove("circuit_1.aig");
    remove("circuit_2.aig");
    remove("1.aag");
    remove("2.aag");
    remove("circuit_1.aag");
    remove("circuit_2.aag");
    remove("name");
    remove("support");

    parser(circuit_file1, "1.v");
    parser(circuit_file2, "2.v");

    // abc
    write_aig();

    remove("1.v");
    remove("2.v");

    // aigtoaig
    aigtoaig("1.aig", "1.aag");
    aigtoaig("2.aig", "2.aag");
    aigtoaig("circuit_1.aig", "circuit_1.aag");
    aigtoaig("circuit_2.aig", "circuit_2.aag");

    remove("1.aig");
    remove("2.aig");
    remove("circuit_1.aig");
    remove("circuit_2.aig");

    // aig_map
    ofstream out_file("name");
    mapping("1.aag", out_file);
    mapping("2.aag", out_file);
    out_file.close();

    // satTest
    BMatchSolver bmatchSolver;

    ifstream portMapping("name");
    ifstream aag1("1.aag");
    ifstream aag2("2.aag");
    ifstream support("support");
    ifstream bus(input);

    bmatchSolver.init(portMapping, aag1, aag2, match);
    bmatchSolver.genFuncSupport(support);
    bmatchSolver.inputPreprocess();
    bmatchSolver.outputPreprocess();
    // for (int i = 0; i < 10; ++i)
    // bmatchSolver.simulate();
    bmatchSolver.readBusInfo(bus, true);
    bmatchSolver.readBusInfo(bus, false);
    bmatchSolver.printInfo();
    int temp;
    //bmatchSolver.busConstraint();
    //cerr << "Enter 1 for bus constraint: ";
    //cin >> temp;
    //if (temp == 1)
        //bmatchSolver.busConstraint();
    
    cerr << "Enter 1 for interactive mode: ";
    int interactive;
    cin >> interactive;
    if (interactive == 1) {
        bmatchSolver.interactiveSolve();
    }
    else {
        bmatchSolver.run();
        cout << "finish run" << endl;
    }
    // bmatchSolver.testOutputMgr();



    remove("1.aag");
    remove("2.aag");
    remove("circuit_1.aag");
    remove("circuit_2.aag");
    remove("name");
    remove("support");
    cout << "program done" << endl;
}