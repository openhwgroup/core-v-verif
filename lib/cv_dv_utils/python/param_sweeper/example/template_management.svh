
class template_management extends uvm_object;

	//Constructor
	function new(string name="template_management");
		super.new(name);
	endfunction

	function void write(string param[string], string template_file, string output_file);
		search_replace_file(template_file,output_file,param);
	endfunction

endclass
