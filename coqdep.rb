ARGV.each do |file_name|
  File.open(file_name, 'r') do |file|
    dir = File.dirname(file)
    Dir.chdir(dir)
    print (file_name + "o: " + file_name + " ")
    file.each_line do |line|
      result = / *Require *Import *(.*\.)* */.match(line)
      if result != nil then
        if (File.file?(result[1] + "v") || File.file?(result[1] + "v.erb")) then
          print (result[1] + "vo ")
        end
      end
    end
    puts ("\n\tcoqc " + file_name)
  end
end
